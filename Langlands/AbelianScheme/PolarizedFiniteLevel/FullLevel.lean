import Langlands.AbelianScheme.Tate.GeometricTorsionReduction
import Langlands.AbelianScheme.BaseChangeCoherence
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Ordered full finite level on actual abelian schemes -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' S'' : Scheme.{u}} {A B C : AbelianScheme S} {g n : ℕ}

/-- An ordered tuple of actual sections in the kernel of multiplication by `n`. -/
abbrev SectionTuple (A : AbelianScheme S) (g n : ℕ) :=
  Fin (2 * g) → Level A.toGrp (Over.mk (𝟙 S)) n

/-- Restrict the entire ordered tuple to the specified actual geometric fibre. -/
def fibreTuple (v : SectionTuple A g n) {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    Fin (2 * g) → Level A.toGrp (Over.mk s) n :=
  fun i => levelRestrict A.toGrp (Over.homMk s (by simp)) n (v i)

/-- Full level means a basis at every algebraically closed field-valued point.
No basis of the module of global sections is required. -/
def IsFull (v : SectionTuple A g n) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
    ∃ b : Module.Basis (Fin (2 * g)) (ZMod n) (Level A.toGrp (Over.mk s) n),
      ∀ i, b i = fibreTuple v s i

/-- An actual ordered full-level structure, without an existence assertion. -/
structure FullLevel (A : AbelianScheme S) (g n : ℕ) where
  sections : SectionTuple A g n
  full : IsFull sections

/-- The basis belonging to the given tuple on the specified geometric fibre. -/
def FullLevel.fibreBasis (v : FullLevel A g n) (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    Module.Basis (Fin (2 * g)) (ZMod n) (Level A.toGrp (Over.mk s) n) :=
  Classical.choose (v.full K s)

@[simp] theorem FullLevel.fibreBasis_apply (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (i : Fin (2 * g)) :
    v.fibreBasis K s i = fibreTuple v.sections s i :=
  Classical.choose_spec (v.full K s) i

/-- The required isomorphism from the standard finite free residue module. -/
def FullLevel.fibreCoordinates (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
    (Fin (2 * g) → ZMod n) ≃ₗ[ZMod n] Level A.toGrp (Over.mk s) n :=
  (v.fibreBasis K s).equivFun.symm

/-- These coordinates are precisely the linear-combination map of the tuple. -/
theorem FullLevel.fibreCoordinates_apply (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Fin (2 * g) → ZMod n) :
    v.fibreCoordinates K s a = ∑ i, a i • fibreTuple v.sections s i := by
  simp [FullLevel.fibreCoordinates]

@[simp] theorem FullLevel.fibreCoordinates_single (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (i : Fin (2 * g)) :
    v.fibreCoordinates K s (Pi.single i 1) = fibreTuple v.sections s i := by
  rw [FullLevel.fibreCoordinates_apply]
  simp

/-- An actual abelian-scheme isomorphism gives linear equivalences on actual torsion. -/
def levelIsoLinear (e : A ≅ B) (T : Over S) (n : ℕ) :
    Level A.toGrp T n ≃ₗ[ZMod n] Level B.toGrp T n where
  toFun := levelMap T (groupHom e.hom) n
  invFun := levelMap T (groupHom e.inv) n
  left_inv x := by
    apply toSection_injective A.toGrp T n
    change ((Additive.toMul x).val ≫ (groupHom e.hom).hom.hom) ≫
      (groupHom e.inv).hom.hom = (Additive.toMul x).val
    rw [Category.assoc]
    change (Additive.toMul x).val ≫ (groupHom (e.hom ≫ e.inv)).hom.hom = _
    rw [e.hom_inv_id]
    exact Category.comp_id _
  right_inv x := by
    apply toSection_injective B.toGrp T n
    change ((Additive.toMul x).val ≫ (groupHom e.inv).hom.hom) ≫
      (groupHom e.hom).hom.hom = (Additive.toMul x).val
    rw [Category.assoc]
    change (Additive.toMul x).val ≫ (groupHom (e.inv ≫ e.hom)).hom.hom = _
    rw [e.inv_hom_id]
    exact Category.comp_id _
  map_add' := (levelMap T (groupHom e.hom) n).map_add
  map_smul' := ZMod.map_smul (levelMap T (groupHom e.hom) n)

/-- Carry an ordered tuple by an actual homomorphism. -/
def mapTuple (f : A ⟶ B) (v : SectionTuple A g n) : SectionTuple B g n :=
  fun i => levelMap (Over.mk (𝟙 S)) (groupHom f) n (v i)

/-- A global actual homomorphism commutes with restriction of its sections. -/
theorem fibreTuple_map (f : A ⟶ B) (v : SectionTuple A g n)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (i : Fin (2 * g)) :
    fibreTuple (mapTuple f v) s i =
      levelMap (Over.mk s) (groupHom f) n (fibreTuple v s i) := by
  apply toSection_injective B.toGrp (Over.mk s) n
  exact (Category.assoc (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))
    (Additive.toMul (v i)).val (groupHom f).hom.hom).symm

/-- Full level is preserved by actual isomorphisms. -/
theorem IsFull.mapIso {v : SectionTuple A g n} (h : IsFull v) (e : A ≅ B) :
    IsFull (mapTuple e.hom v) := by
  intro K _ _ s
  obtain ⟨b, hb⟩ := h K s
  refine ⟨b.map (levelIsoLinear e (Over.mk s) n), ?_⟩
  intro i
  change levelIsoLinear e (Over.mk s) n (b i) = _
  rw [hb i]
  exact (fibreTuple_map e.hom v s i).symm

/-- Transport a supplied full-level structure along an actual isomorphism. -/
def FullLevel.mapIso (v : FullLevel A g n) (e : A ≅ B) : FullLevel B g n :=
  ⟨mapTuple e.hom v.sections, v.full.mapIso e⟩

/-- Actual pullback of an ordered tuple of global torsion sections. -/
def pullbackTuple (b : S' ⟶ S) (v : SectionTuple A g n) :
    SectionTuple ((baseChange b).obj A) g n :=
  fun i => (levelBaseChange b A.toGrp (Over.mk (𝟙 S')) n).symm
    (levelRestrict A.toGrp (Over.homMk b (by simp)) n (v i))

/-- At every point of the new base, pullback sections are the original sections
at its composite point, under the actual torsion base-change comparison. -/
theorem fibreTuple_pullback (b : S' ⟶ S) (v : SectionTuple A g n)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S') (i : Fin (2 * g)) :
    levelBaseChange b A.toGrp (Over.mk s) n
        (fibreTuple (pullbackTuple b v) s i) = fibreTuple v (s ≫ b) i := by
  unfold fibreTuple
  erw [levelBaseChange_testRestrict]
  unfold pullbackTuple
  rw [AddEquiv.apply_symm_apply]
  apply toSection_injective A.toGrp (Over.mk (s ≫ b)) n
  exact (Category.assoc (Over.homMk s (by simp) :
      Over.mk (s ≫ b) ⟶ (Over.map b).obj (Over.mk (𝟙 S')))
    (Over.homMk b (by simp) : (Over.map b).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S))
    (Additive.toMul (v i)).val).symm

/-- Fullness on every geometric fibre is preserved by arbitrary base change.
This uses no torsion-rank or level-existence theorem. -/
theorem IsFull.pullback {v : SectionTuple A g n} (h : IsFull v) (b : S' ⟶ S) :
    IsFull (pullbackTuple b v) := by
  intro K _ _ s
  obtain ⟨bs, hbs⟩ := h K (s ≫ b)
  refine ⟨bs.map (levelBaseChangeLinear A.toGrp b (Over.mk s) n).symm, ?_⟩
  intro i
  apply (levelBaseChangeLinear A.toGrp b (Over.mk s) n).injective
  change (levelBaseChangeLinear A.toGrp b (Over.mk s) n)
    ((levelBaseChangeLinear A.toGrp b (Over.mk s) n).symm (bs i)) = _
  rw [LinearEquiv.apply_symm_apply, hbs i]
  exact (fibreTuple_pullback b v s i).symm

/-- Pull back a supplied full-level structure along any actual base morphism. -/
def FullLevel.pullback (v : FullLevel A g n) (b : S' ⟶ S) :
    FullLevel ((baseChange b).obj A) g n :=
  ⟨pullbackTuple b v.sections, v.full.pullback b⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
