import Langlands.WeilDeligne.Parameters
import Langlands.Weil.Representation.DirectSum

/-!
# Finite direct sums of Weil–Deligne pairs

For a family indexed by a finite type, the carrier is the actual direct sum
`⨁ i, A i`, the Weil action is componentwise and the monodromy is the
componentwise operator `DirectSum.lmap (fun i => N_i)`. Nilpotence and covariance
are proved, not assumed. The empty family gives the rank-zero pair.
-/

noncomputable section

universe uK uG uV uι

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

section LinearAlgebra

variable {K : Type uK} [Field K] {ι : Type uι} {V : ι → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Componentwise maps multiply componentwise. -/
theorem lmap_mul (f g : ∀ i, Module.End K (V i)) :
    DirectSum.lmap (fun i => f i * g i) = DirectSum.lmap f * DirectSum.lmap g :=
  DirectSum.lmap_comp g f

/-- Componentwise powers. -/
theorem lmap_pow (f : ∀ i, Module.End K (V i)) (n : ℕ) :
    DirectSum.lmap f ^ n = DirectSum.lmap fun i => f i ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact DirectSum.lmap_id.symm
  | succ n ih =>
    rw [pow_succ, ih, ← lmap_mul]
    simp only [pow_succ]

/-- Componentwise scalar multiples. -/
theorem lmap_smul (c : K) (f : ∀ i, Module.End K (V i)) :
    DirectSum.lmap (fun i => c • f i) = c • DirectSum.lmap f := by
  apply LinearMap.ext
  intro x
  apply DirectSum.ext
  intro i
  rfl

/-- The componentwise zero map is zero. -/
theorem lmap_zero :
    DirectSum.lmap (fun i => (0 : Module.End K (V i))) = 0 := by
  apply LinearMap.ext
  intro x
  apply DirectSum.ext
  intro i
  rfl

end LinearAlgebra

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}
  {ι : Type uι} [Fintype ι]

/-- The direct sum of a finite family of pairs, with componentwise monodromy. -/
def directSum (A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uG, max uι uV} K G ν where
  toFiniteRepresentation :=
    FiniteRepresentation.directSum fun i => (A i).toFiniteRepresentation
  monodromy := DirectSum.lmap fun i => (A i).monodromy
  nilpotent := by
    choose n hn using fun i => (A i).nilpotent
    refine ⟨∑ i, n i, ?_⟩
    change DirectSum.lmap (fun i => (A i).monodromy) ^ (∑ i, n i) = 0
    rw [lmap_pow]
    have h : ∀ i, (A i).monodromy ^ (∑ j, n j) = 0 := fun i =>
      pow_eq_zero_of_le (Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
        (Finset.mem_univ i)) (hn i)
    simp only [h]
    exact lmap_zero
  covariance g := by
    change DirectSum.lmap (fun i => (A i).representation g) *
        DirectSum.lmap (fun i => (A i).monodromy) *
        DirectSum.lmap (fun i => (A i).representation g⁻¹) =
      (ν g : K) • DirectSum.lmap (fun i => (A i).monodromy)
    rw [← lmap_mul, ← lmap_mul, ← lmap_smul]
    congr 1
    funext i
    exact (A i).covariance g

/-- The monodromy acts componentwise. -/
theorem directSum_monodromy (A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    (directSum A).monodromy = DirectSum.lmap fun i => (A i).monodromy :=
  rfl

/-- The componentwise direct sum of a family of pair morphisms. -/
def directSumMap {A B : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    (f : ∀ i, Hom (A i) (B i)) : Hom (directSum A) (directSum B) where
  intertwiner := FiniteRepresentation.directSumMap fun i => (f i).intertwiner
  comm_monodromy := by
    change DirectSum.lmap (fun i => (f i).intertwiner.toLinearMap) ∘ₗ
        DirectSum.lmap (fun i => (A i).monodromy) =
      DirectSum.lmap (fun i => (B i).monodromy) ∘ₗ
        DirectSum.lmap (fun i => (f i).intertwiner.toLinearMap)
    rw [← DirectSum.lmap_comp, ← DirectSum.lmap_comp]
    congr 1
    funext i
    exact (f i).comm_monodromy

/-- The direct sum is a functor on finite families of pairs. -/
def directSumFunctor :
    (ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) ⥤
      WeilDeligneRepresentation.{uK, uG, max uι uV} K G ν where
  obj := directSum
  map f := directSumMap f
  map_id _ := by
    apply Hom.ext
    apply Representation.IntertwiningMap.ext
    exact DirectSum.lmap_id
  map_comp _ _ := by
    apply Hom.ext
    apply Representation.IntertwiningMap.ext
    exact DirectSum.lmap_comp _ _

/-- A family of genuine pair equivalences gives one of direct sums. -/
def directSumEquiv {A B : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    (e : ∀ i, Equiv (A i) (B i)) : Equiv (directSum A) (directSum B) :=
  Equiv.ofIso (directSumFunctor.mapIso (Pi.isoMk fun i => (e i).toIso))

/-- The rank of a direct sum of pairs is the sum of the ranks. -/
theorem rank_directSum (A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    (directSum A).rank = ∑ i, (A i).rank :=
  FiniteRepresentation.rank_directSum fun i => (A i).toFiniteRepresentation

variable [DecidableEq ι]

/-- Direct sum on finite families of genuine pair classes. -/
def directSumClass (c : ι → IsomorphismClasses.{uK, uG, uV} K G ν) :
    IsomorphismClasses.{uK, uG, max uι uV} K G ν :=
  Quotient.lift (fun A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν =>
      classOf (directSum A))
    (fun _ _ h => (classOf_eq_iff _ _).mpr ⟨directSumEquiv fun i => (h i).some⟩)
    (Quotient.finChoice (S := fun _ => isomorphismSetoid) c)

/-- The class operation is computed by representatives. -/
theorem directSumClass_classOf (A : ι → WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    directSumClass (fun i => classOf (A i)) = classOf (directSum A) := by
  unfold directSumClass
  rw [show (fun i => classOf (A i)) =
      (fun i => (⟦A i⟧ : IsomorphismClasses K G ν)) from rfl, Quotient.finChoice_eq]
  rfl

section Complex

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ν : G →* ℂˣ} (I : Subgroup G)

/-- Direct sum on actual open-inertia parameter objects. -/
def parameterDirectSum (A : ι → ParameterObjects.{uG, uV} (ν := ν) I) :
    ParameterObjects.{uG, max uι uV} (ν := ν) I :=
  ⟨directSum fun i => (A i).val,
    FiniteRepresentation.hasOpenInertiaKernel_directSum I fun i => (A i).property⟩

/-- Direct sum on finite families of genuine parameter classes. -/
def parameterDirectSumClass (c : ι → ParameterClasses.{uG, uV} (ν := ν) I) :
    ParameterClasses.{uG, max uι uV} (ν := ν) I :=
  Quotient.lift (fun A => Quotient.mk _ (parameterDirectSum I A))
    (fun _ _ h => Quotient.sound ⟨directSumEquiv fun i => (h i).some⟩)
    (Quotient.finChoice (S := fun _ => parameterSetoid I) c)

end Complex

end Langlands.WeilDeligneRepresentation
