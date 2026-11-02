import Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability
import Langlands.GroupScheme.Dynamic.SchemeCoordinates

/-! # The limit, kernel and multiplication isomorphism on the GL block subgroup schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ)

/-- The block diagonal limit, as a homomorphism between the concrete block group schemes. -/
def blockLimitHom : blockParabolicScheme n R e ⟶ blockLeviScheme n R e :=
  Dynamic.limitGroupHom (isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (isRepresentedBy_centralizer_diagonalCocharacter n R e)

/-- The block Levi inclusion into the block parabolic group scheme. -/
def blockLeviToParabolic : blockLeviScheme n R e ⟶ blockParabolicScheme n R e :=
  Dynamic.centralizerToParabolic (isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (isRepresentedBy_centralizer_diagonalCocharacter n R e)

theorem blockLeviToParabolic_comp :
    blockLeviToParabolic n R e ≫ blockParabolicHom n R e = blockLeviHom n R e :=
  Dynamic.centralizerToParabolic_comp _ _

theorem blockLeviToParabolic_comp_blockLimitHom :
    blockLeviToParabolic n R e ≫ blockLimitHom n R e = 𝟙 (blockLeviScheme n R e) :=
  Dynamic.centralizerToParabolic_comp_limitGroupHom _ _

theorem blockLimitHom_comp {T : Over (Spec R)} (p : T ⟶ (blockParabolicScheme n R e).X) :
    (p ≫ (blockLimitHom n R e).hom.hom) ≫ (blockLeviHom n R e).hom.hom =
      Dynamic.limit (diagonalCocharacter n R e)
        ((isRepresentedBy_parabolic_diagonalCocharacter n R e).pointsEquiv T p) :=
  Dynamic.limitGroupHom_comp _ _ p

/-- On every test scheme the limit is the existing block diagonal projection of matrices. -/
theorem pointsEquiv_blockLimitHom {T : Over (Spec R)}
    (p : T ⟶ (blockParabolicScheme n R e).X) :
    pointsEquiv n R T
        ((p ≫ (blockLimitHom n R e).hom.hom) ≫ (blockLeviHom n R e).hom.hom) =
      blockLeviProjection Γ(T.left, ⊤) e
        ⟨pointsEquiv n R T (p ≫ (blockParabolicHom n R e).hom.hom),
          ((isRepresentedBy_blockParabolic n R e).pointsEquiv T p).2⟩ := by
  rw [blockLimitHom_comp]
  obtain ⟨_, hl⟩ := (hasLimit_diagonalCocharacter_iff e).1
    (Dynamic.hasLimit_limit (diagonalCocharacter n R e)
      ((isRepresentedBy_parabolic_diagonalCocharacter n R e).pointsEquiv T p))
  exact hl

/-- The block unipotent group scheme is the actual scheme-theoretic kernel of the limit. -/
def blockUnipotentIsoKernel :
    blockUnipotentScheme n R e ≅ kernel (blockLimitHom n R e) :=
  Dynamic.unipotentIsoKernel
    (hP := isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (hZ := isRepresentedBy_centralizer_diagonalCocharacter n R e)
    (isRepresentedBy_unipotent_diagonalCocharacter n R e)

theorem blockUnipotentIsoKernel_hom_comp :
    (blockUnipotentIsoKernel n R e).hom ≫ kernelι (blockLimitHom n R e) ≫
        blockParabolicHom n R e = blockUnipotentHom n R e :=
  Dynamic.unipotentIsoKernel_hom_comp _

/-- Multiplication of the concrete block unipotent and block Levi schemes is an isomorphism. -/
def blockMultiplicationIso :
    (blockUnipotentScheme n R e).X ⊗ (blockLeviScheme n R e).X ≅
      (blockParabolicScheme n R e).X :=
  Dynamic.multiplicationIso (isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (isRepresentedBy_centralizer_diagonalCocharacter n R e)
    (isRepresentedBy_unipotent_diagonalCocharacter n R e)

theorem blockMultiplicationIso_hom_comp :
    (blockMultiplicationIso n R e).hom ≫ (blockParabolicHom n R e).hom.hom =
      (fst (blockUnipotentScheme n R e).X (blockLeviScheme n R e).X ≫
        (blockUnipotentHom n R e).hom.hom) *
      (snd (blockUnipotentScheme n R e).X (blockLeviScheme n R e).X ≫
        (blockLeviHom n R e).hom.hom) :=
  Dynamic.multiplication_comp (isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (isRepresentedBy_centralizer_diagonalCocharacter n R e)
    (isRepresentedBy_unipotent_diagonalCocharacter n R e)

theorem lift_comp_blockMultiplicationIso_hom_comp {T : Over (Spec R)}
    (u : T ⟶ (blockUnipotentScheme n R e).X) (z : T ⟶ (blockLeviScheme n R e).X) :
    (lift u z ≫ (blockMultiplicationIso n R e).hom) ≫ (blockParabolicHom n R e).hom.hom =
      (u ≫ (blockUnipotentHom n R e).hom.hom) * (z ≫ (blockLeviHom n R e).hom.hom) := by
  rw [Category.assoc, blockMultiplicationIso_hom_comp, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc]

/-- The concrete multiplication is ordinary matrix multiplication on every test scheme. -/
theorem pointsEquiv_blockMultiplicationIso_hom {T : Over (Spec R)}
    (u : T ⟶ (blockUnipotentScheme n R e).X) (z : T ⟶ (blockLeviScheme n R e).X) :
    pointsEquiv n R T
        ((lift u z ≫ (blockMultiplicationIso n R e).hom) ≫ (blockParabolicHom n R e).hom.hom) =
      pointsEquiv n R T (u ≫ (blockUnipotentHom n R e).hom.hom) *
        pointsEquiv n R T (z ≫ (blockLeviHom n R e).hom.hom) := by
  rw [lift_comp_blockMultiplicationIso_hom_comp, map_mul]

theorem blockMultiplicationIso_inv_snd :
    (blockMultiplicationIso n R e).inv ≫
        snd (blockUnipotentScheme n R e).X (blockLeviScheme n R e).X =
      (blockLimitHom n R e).hom.hom :=
  Dynamic.multiplicationIso_inv_snd (isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (isRepresentedBy_centralizer_diagonalCocharacter n R e)
    (isRepresentedBy_unipotent_diagonalCocharacter n R e)

theorem blockMultiplicationIso_inv_fst_comp :
    ((blockMultiplicationIso n R e).inv ≫
        fst (blockUnipotentScheme n R e).X (blockLeviScheme n R e).X) ≫
        (blockUnipotentHom n R e).hom.hom =
      (blockParabolicHom n R e).hom.hom *
        ((blockLimitHom n R e).hom.hom ≫ (blockLeviHom n R e).hom.hom)⁻¹ :=
  Dynamic.multiplicationIso_inv_fst_comp (isRepresentedBy_parabolic_diagonalCocharacter n R e)
    (isRepresentedBy_centralizer_diagonalCocharacter n R e)
    (isRepresentedBy_unipotent_diagonalCocharacter n R e)

end Langlands.GroupScheme.GeneralLinear
