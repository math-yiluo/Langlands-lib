import Langlands.Weil.Representation.Predicates
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite direct sums of finite-dimensional representations

For a family indexed by a finite type, the carrier is Mathlib's direct sum
`⨁ i, A i` of the actual carriers and the action is `Representation.directSum`.
Rank zero and the empty family are allowed.
-/

noncomputable section

universe uK uG uV uι

open CategoryTheory

namespace Langlands.FiniteRepresentation

section Algebraic

variable {K : Type uK} {G : Type uG} [Field K] [Monoid G] {ι : Type uι} [Fintype ι]

/-- The direct sum of a finite family, on the actual carrier `⨁ i, A i`. -/
def directSum (A : ι → FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.{uK, uG, max uι uV} K G :=
  of (Representation.directSum fun i => (A i).representation)

/-- The action is componentwise. -/
theorem directSum_representation (A : ι → FiniteRepresentation.{uK, uG, uV} K G) (g : G) :
    (directSum A).representation g = DirectSum.lmap fun i => (A i).representation g :=
  rfl

/-- The componentwise direct sum of a family of linear intertwiners. -/
def directSumMap {A B : ι → FiniteRepresentation.{uK, uG, uV} K G}
    (f : ∀ i, (A i).representation.IntertwiningMap (B i).representation) :
    (directSum A).representation.IntertwiningMap (directSum B).representation where
  toLinearMap := DirectSum.lmap fun i => (f i).toLinearMap
  isIntertwining' g := by
    change DirectSum.lmap (fun i => (f i).toLinearMap) ∘ₗ
        DirectSum.lmap (fun i => (A i).representation g) =
      DirectSum.lmap (fun i => (B i).representation g) ∘ₗ
        DirectSum.lmap (fun i => (f i).toLinearMap)
    rw [← DirectSum.lmap_comp, ← DirectSum.lmap_comp]
    congr 1
    funext i
    exact (f i).isIntertwining' g

/-- The direct sum is a functor on finite families of representations. -/
def directSumFunctor :
    (ι → FiniteRepresentation.{uK, uG, uV} K G) ⥤
      FiniteRepresentation.{uK, uG, max uι uV} K G where
  obj := directSum
  map f := (homEquiv _ _).symm (directSumMap fun i => homEquiv _ _ (f i))
  map_id _ := by
    apply (homEquiv _ _).injective
    apply Representation.IntertwiningMap.ext
    exact DirectSum.lmap_id
  map_comp _ _ := by
    apply (homEquiv _ _).injective
    apply Representation.IntertwiningMap.ext
    exact DirectSum.lmap_comp _ _

/-- A family of genuine representation equivalences gives one of direct sums. -/
def directSumEquiv {A B : ι → FiniteRepresentation.{uK, uG, uV} K G}
    (e : ∀ i, Equiv (A i) (B i)) : Equiv (directSum A) (directSum B) :=
  equivOfIso (directSumFunctor.mapIso (Pi.isoMk fun i => isoOfEquiv (e i)))

/-- The rank of a direct sum is the sum of the ranks. -/
theorem rank_directSum (A : ι → FiniteRepresentation.{uK, uG, uV} K G) :
    (directSum A).rank = ∑ i, (A i).rank :=
  Module.finrank_directSum K fun i => (A i : Type uV)

variable [DecidableEq ι]

/-- Direct sum on finite families of genuine isomorphism classes. -/
def directSumClass (c : ι → IsomorphismClasses.{uK, uG, uV} K G) :
    IsomorphismClasses.{uK, uG, max uι uV} K G :=
  Quotient.lift (fun A : ι → FiniteRepresentation.{uK, uG, uV} K G => classOf (directSum A))
    (fun _ _ h => (classOf_eq_iff _ _).mpr ⟨directSumEquiv fun i => (h i).some⟩)
    (Quotient.finChoice (S := fun _ => isomorphismSetoid) c)

/-- The class operation is computed by representatives. -/
theorem directSumClass_classOf (A : ι → FiniteRepresentation.{uK, uG, uV} K G) :
    directSumClass (fun i => classOf (A i)) = classOf (directSum A) := by
  unfold directSumClass
  rw [show (fun i => classOf (A i)) = (fun i => (⟦A i⟧ : IsomorphismClasses K G)) from rfl,
    Quotient.finChoice_eq]
  rfl

end Algebraic

section OpenInertia

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (I : Subgroup G) {ι : Type uι} [Fintype ι]

/-- A finite direct sum of open-inertia representations has open inertia
kernel: it contains the finite intersection of the component kernels. -/
theorem hasOpenInertiaKernel_directSum {A : ι → FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : ∀ i, (A i).HasOpenInertiaKernel I) : (directSum A).HasOpenInertiaKernel I := by
  apply Subgroup.isOpen_mono (H₁ := ⨅ i, (A i).inertiaKernel I)
    (H₂ := (directSum A).inertiaKernel I)
  · intro x hx
    have h : ∀ i, (A i).representation (x : G) = 1 := fun i => (Subgroup.mem_iInf.mp hx) i
    change DirectSum.lmap (fun i => (A i).representation (x : G)) = 1
    simp only [h]
    exact DirectSum.lmap_id
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hA

/-- Direct sum on actual open-inertia objects. -/
def openInertiaDirectSum (A : ι → OpenInertiaObjects.{uG, uV} I) :
    OpenInertiaObjects.{uG, max uι uV} I :=
  ⟨directSum fun i => (A i).val, hasOpenInertiaKernel_directSum I fun i => (A i).property⟩

variable [DecidableEq ι]

/-- Direct sum on finite families of genuine open-inertia classes. -/
def openInertiaDirectSumClass
    (c : ι → IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.HasOpenInertiaKernel I)) :
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, max uι uV} ℂ G => A.HasOpenInertiaKernel I) :=
  Quotient.lift (fun A => Quotient.mk _ (openInertiaDirectSum I A))
    (fun _ _ h => Quotient.sound ⟨directSumEquiv fun i => (h i).some⟩)
    (Quotient.finChoice (S := fun _ => propertyIsomorphismSetoid _) c)

end OpenInertia

end Langlands.FiniteRepresentation
