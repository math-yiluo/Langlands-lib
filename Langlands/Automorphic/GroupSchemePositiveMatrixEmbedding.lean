import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.MatrixRepresentationRationalPoints

/-! # Positive matrix size for automorphic functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A closed matrix embedding of size zero forces every group of test points
to be trivial. -/
private theorem subsingleton_points_of_closed_zeroMatrix
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho)
    (T : Over (Spec (CommRingCat.of F))) : Subsingleton (T ⟶ G.X) := by
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : Mono rho.hom.hom := Over.mono_of_mono_left _
  exact ⟨fun x y => rho.pointMatrix_injective T (Subsingleton.elim _ _)⟩

private theorem isClosedSubgroup_trivial_of_closed_zeroMatrix
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    IsClosedSubgroup (MatrixRepresentation.trivial G (Fin 1)) := by
  have hleft : toUnit G.X ≫ η[G.X] = 𝟙 G.X :=
    (subsingleton_points_of_closed_zeroMatrix rho hrho G.X).elim _ _
  have hright : η[G.X] ≫ toUnit G.X = 𝟙 _ :=
    toUnit_unique _ _
  let : IsIso (toUnit G.X) := ⟨⟨η[G.X], hleft, hright⟩⟩
  have : IsIso ((Over.forget (Spec (CommRingCat.of F))).map (toUnit G.X)) := inferInstance
  let : IsIso (toUnit G.X).left := this
  let H := GeneralLinear.groupScheme (Fin 1) (CommRingCat.of F)
  let : IsClosedImmersion η[H.X].left := unit_isClosedImmersion_of_subsingleton H
  change IsClosedImmersion ((toUnit G.X).left ≫ η[H.X].left)
  infer_instance

variable [NumberField F] [IsAffine G.X.left]

/-- Given a closed matrix embedding, there is a positive-size closed embedding
for which the same invariant functions are automorphic. The matrix size
can change only in the case of a trivial adelic group. -/
theorem exists_positiveMatrixEmbedding_of_isClosedSubgroup
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    ∃ (N' : ℕ) (rho' : MatrixRepresentation G (Fin N')), 0 < N' ∧ IsClosedSubgroup rho' ∧
      ∀ (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
        (φ : AdelicGroupPoints F G → ℂ),
        IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ ↔
        IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho' φ := by
  cases N with
  | zero =>
    let rho' := MatrixRepresentation.trivial G (Fin 1)
    have hG : Subsingleton (AdelicGroupPoints F G) :=
      subsingleton_points_of_closed_zeroMatrix rho hrho _
    refine ⟨1, rho', zero_lt_one, isClosedSubgroup_trivial_of_closed_zeroMatrix rho hrho, ?_⟩
    intro Γ Kinf φ
    have hmoderate {m : ℕ} (r : MatrixRepresentation G (Fin m)) :
        HasModerateGrowthFunction F G r φ := by
      refine ⟨‖φ 1‖ + 1, by positivity, 0, fun g => ?_⟩
      rw [hG.elim g 1, Real.rpow_zero, mul_one]
      exact le_add_of_nonneg_right zero_le_one
    exact ⟨fun hφ => ⟨hφ.1, hφ.2.1, hφ.2.2.1, hφ.2.2.2.1, hmoderate rho'⟩,
      fun hφ => ⟨hφ.1, hφ.2.1, hφ.2.2.1, hφ.2.2.2.1, hmoderate rho⟩⟩
  | succ N =>
    exact ⟨N + 1, rho, Nat.succ_pos N, hrho, fun _ _ _ => Iff.rfl⟩

/-- Every prescribed closed embedding can be replaced by a positive-size
closed embedding preserving the automorphy predicates of all functions. -/
def PositiveMatrixEmbeddingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
    ∃ (N' : ℕ) (rho' : MatrixRepresentation G (Fin N')), 0 < N' ∧ IsClosedSubgroup rho' ∧
      ∀ (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
        (φ : AdelicGroupPoints F G → ℂ),
        IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ ↔
        IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho' φ

theorem positiveMatrixEmbedding : PositiveMatrixEmbeddingStatement.{u} := by
  intro F _ _ G _ N d rho hsmooth hcalc hrho
  exact exists_positiveMatrixEmbedding_of_isClosedSubgroup rho hrho hsmooth hcalc

end Langlands.Automorphic.GroupSchemeFunctions
