import Langlands.GroupScheme.Quaternionic.SymplecticReducedNorm

/-! # Affine tensor coordinates for the actual symplectic point image -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] (σ : FirstKindInvolution F D)
  {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n D)

local notation "A" => Matrix n n D
local notation "B" => Module.finBasis F A
local notation "Tₐ" R => Functor.obj (algSpec (CommRingCat.of F)) (op R)

/-- The exact unitary subgroup of the tensor algebra's units. -/
abbrev tensorUnitaryGroup (R : Type u) [CommRing R] [Algebra F R] : Subgroup (R ⊗[F] A)ˣ :=
  IsometryCut.isometrySubgroup (τ := σ.matrix n) (M := ⊥) IsometryCut.isStable_bot H R

/-- The unitary group's affine points recover its actual tensor unitary subgroup. -/
def unitaryAffinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of F)) :
    (σ.unitaryGroup H).affinePoints R ≃* σ.tensorUnitaryGroup H R :=
  Corepresented.affinePointsEquiv _
    (Corepresented.cutCorepresentableBy
      (IsometryCut.isCutOutBy (τ := σ.matrix n) (M := ⊥) IsometryCut.isStable_bot H)) R

/-- The unitary affine point comparison has the prescribed ambient tensor unit. -/
theorem unitaryAffinePointsEquiv_val (R : CommAlgCat.{u} (CommRingCat.of F))
    (x : (σ.unitaryGroup H).affinePoints R) :
    (σ.unitaryAffinePointsEquiv H R x).val =
      FiniteAlgebraUnits.affinePointsEquiv B R (x ≫ (σ.unitaryGroupι H).hom.hom) := by
  change _ = Corepresented.affinePointsEquiv _ (FiniteAlgebraUnits.corepresentableBy B) R
    (x ≫ (Corepresented.cutHom _).hom.hom)
  rw [Corepresented.cutHom, Corepresented.groupSchemeMap_affinePoints]
  rfl

/-- An affine point of the ambient unit group lifts to a unitary affine point precisely
when its affine tensor unit preserves the base-changed Gram matrix. -/
theorem mem_range_unitaryGroupι_affine_iff (R : CommAlgCat.{u} (CommRingCat.of F))
    (x : (FiniteAlgebraUnits.groupScheme B).affinePoints R) :
    x ∈ (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier (Tₐ R) ↔
      IsometryCut.defect (σ.matrix n) H
        ((FiniteAlgebraUnits.affinePointsEquiv B R x : (R ⊗[F] A)ˣ) : R ⊗[F] A) = 0 := by
  let E := FiniteAlgebraUnits.affinePointsEquiv B R
  let e := σ.unitaryAffinePointsEquiv H R
  have hmem (v : (R ⊗[F] A)ˣ) : v ∈ σ.tensorUnitaryGroup H R ↔
      IsometryCut.defect (σ.matrix n) H (v : R ⊗[F] A) = 0 := by
    rw [tensorUnitaryGroup, IsometryCut.mem_isometrySubgroup, Submodule.baseChange_bot,
      Submodule.mem_bot]
  rw [SubgroupFunctor.mem_range, ← hmem]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← σ.unitaryAffinePointsEquiv_val H R y]
    exact (e y).property
  · intro h
    let y := e.symm ⟨E x, h⟩
    refine ⟨y, E.injective ?_⟩
    rw [← σ.unitaryAffinePointsEquiv_val H R y]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨E x, h⟩)

variable [Algebra.IsCentral F D] [Nonempty n]

/-- In symplectic type the Gram equation alone characterizes the image of the actual
special unitary inclusion on affine tests. -/
theorem mem_range_symplecticAmbientι_affine_iff
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (R : CommAlgCat.{u} (CommRingCat.of F)) (x : (ambientUnits F D n).affinePoints R) :
    x ∈ (SubgroupFunctor.range (σ.symplecticAmbientι H)).carrier (Tₐ R) ↔
      IsometryCut.defect (σ.matrix n) H
        ((FiniteAlgebraUnits.affinePointsEquiv B R x : (R ⊗[F] A)ˣ) : R ⊗[F] A) = 0 :=
  (symplecticAmbientRange F D σ n H hσ hH hu (Tₐ R) x).trans
    (σ.mem_range_unitaryGroupι_affine_iff H R x)

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
