import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic

/-! # The splitting of `U(1,1)` over `E` carries `λ` to `t ↦ diag(t, t⁻¹)` -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

open Langlands.Shimura.AlgebraInvolution.SchemeModel
attribute [local instance] sectionsSAlgebra sectionsScalarTower

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [IsQuadraticExtension F E]
  {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E) (hc : c ≠ AlgEquiv.refl)

/-- The base change to `Spec E` of a cocharacter of `U(1,1)`, as a cocharacter of `G_E`. -/
def baseChangeCocharacter (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ groupScheme b c) :
    (Gm (Spec (CommRingCat.of E))).toGrp ⟶ baseChangeGroupScheme b c :=
  (Gm.baseChangeIso (scalarBaseMap F E)).inv ≫
    (GroupScheme.baseChange (scalarBaseMap F E)).map χ

/-- On points, the base-changed cocharacter evaluates `χ` on the same unit over `Spec F`. -/
theorem baseChangePointsEquiv_baseChangeCocharacter
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ groupScheme b c)
    (T : Over (Spec (CommRingCat.of E))) (x : T ⟶ (Gm (Spec (CommRingCat.of E))).X) :
    GroupScheme.baseChangePointsEquiv (scalarBaseMap F E) (groupScheme b c) T
        (x ≫ (baseChangeCocharacter b c χ).hom.hom) =
      (Gm.pointsEquiv _ ((Over.map (scalarBaseMap F E)).obj T)).symm
          (Gm.pointsEquiv _ T x) ≫ χ.hom.hom := by
  change GroupScheme.baseChangePointsEquiv (scalarBaseMap F E) (groupScheme b c) T
      ((x ≫ (Gm.baseChangeIso (scalarBaseMap F E)).inv.hom.hom) ≫
        ((GroupScheme.baseChange (scalarBaseMap F E)).map χ).hom.hom) = _
  rw [GroupScheme.baseChangePointsEquiv_comp]
  congr 1
  apply (Gm.pointsEquiv _ ((Over.map (scalarBaseMap F E)).obj T)).injective
  rw [MulEquiv.apply_symm_apply]
  exact Gm.baseChangeUnitsEquiv_baseChangeIso_inv _ T x

/-- The splitting carries the base change of the weight-`(m, -m)` cocharacter to the diagonal
cocharacter of `GL₂` with weights `(m, -m)`. -/
theorem baseChangeCocharacter_weightCocharacter_splittingIso (m : ℤ) :
    baseChangeCocharacter b c (weightCocharacter b c m) ≫ (splittingIso b c hc).hom =
      GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights m) := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv (Fin 2) (CommRingCat.of E) T).injective
  rw [GeneralLinear.pointsEquiv_diagonalCocharacter]
  change GeneralLinear.pointsEquiv (Fin 2) (CommRingCat.of E) T
      ((x ≫ (baseChangeCocharacter b c (weightCocharacter b c m)).hom.hom) ≫
        (splittingIso b c hc).hom.hom.hom) = _
  rw [splittingIso_hom_points]
  apply Units.ext
  ext i j
  rw [basePointsEquiv_apply, baseChangePointsEquiv_baseChangeCocharacter,
    pointsEquiv_weightCocharacter, MulEquiv.apply_symm_apply,
    diagonalUnitary_val ((algΓ (CommRingCat.of F)).obj ((Over.map (scalarBaseMap F E)).obj T)).unop
      c m (Gm.pointsEquiv _ T x),
    GeneralLinear.coe_diagonalUnits, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · have h := tensorSplit_tmul (restrictedSections F E T) c hc (1 : E)
      (((Gm.pointsEquiv _ T x ^ weights m i : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) :
        restrictedSections F E T)
    simp only [map_one] at h
    exact (congrArg Prod.fst h).trans (mul_one _)
  · exact congrArg Prod.fst (map_zero (tensorSplit (restrictedSections F E T) c hc))

/-- The splitting `G_E ≅ GL₂` carries the base change of `λ` to `t ↦ diag(t, t⁻¹)`. -/
theorem baseChangeCocharacter_cocharacter_splittingIso :
    baseChangeCocharacter b c (cocharacter b c) ≫ (splittingIso b c hc).hom =
      GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights 1) :=
  baseChangeCocharacter_weightCocharacter_splittingIso b c hc 1

end Langlands.GroupScheme.QuasiSplitUnitary
