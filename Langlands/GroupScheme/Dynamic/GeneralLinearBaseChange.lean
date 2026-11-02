import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Base change of the diagonal cocharacters of `GL_n`

For a morphism `b : Spec R' ⟶ Spec R` and weights `e : n → ℤ`, the base change of the diagonal
cocharacter `t ↦ diag(t ^ e i)` of `GL_{n,R}`, followed by the Library isomorphism
`(GL_{n,R})_{R'} ≅ GL_{n,R'}`, is the diagonal cocharacter of `GL_{n,R'}`. Consequently the
base changes of `P(λ)`, `Z(λ)` and `U(λ)` for the diagonal cocharacter over `R` are the preimages
of the corresponding subgroup functors over `R'`. The block parabolic, block Levi and block
unipotent subgroup functors base change in the same way.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
  (e : n → ℤ)

/-- On points, the base-change isomorphism of `GL_n` keeps the matrix. -/
theorem pointsEquiv_comp_baseChangeIso_hom {T : Over (Spec R')}
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme n R)).X) :
    pointsEquiv n R' T (x ≫ (baseChangeIso n b).hom.hom.hom) =
      pointsEquiv n R ((Over.map b).obj T) (baseChangePointsEquiv b (groupScheme n R) T x) := by
  rw [baseChangeIso, comp_isoOfPoints_hom, baseChangeGLPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The base change of the diagonal cocharacter of `GL_{n,R}`, followed by
`(GL_{n,R})_{R'} ≅ GL_{n,R'}`, is the diagonal cocharacter of `GL_{n,R'}`. -/
theorem baseChangeCocharacter_diagonalCocharacter :
    Dynamic.baseChangeCocharacter b (diagonalCocharacter n R e) ≫ (baseChangeIso n b).hom =
      diagonalCocharacter n R' e := by
  refine hom_ext_points fun T t => (pointsEquiv n R' T).injective ?_
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_comp_baseChangeIso_hom,
    Dynamic.baseChangePointsEquiv_baseChangeCocharacter, pointsEquiv_diagonalCocharacter,
    pointsEquiv_diagonalCocharacter, ← Gm.baseChangeUnitsEquiv_apply,
    Gm.baseChangeUnitsEquiv_baseChangeIso_inv]
  rfl

/-- The same for the standard cocharacter of an ordered block shape. -/
theorem baseChangeCocharacter_blockShapeCocharacter {N : ℕ}
    (B : Langlands.GeneralLinear.BlockShape N) :
    Dynamic.baseChangeCocharacter b (blockShapeCocharacter B R) ≫ (baseChangeIso (Fin N) b).hom =
      blockShapeCocharacter B R' :=
  baseChangeCocharacter_diagonalCocharacter b _

/-- The block parabolic subgroup functor commutes with base change. -/
theorem blockParabolic_baseChange :
    (blockParabolic n R e).baseChange b =
      (blockParabolic n R' e).comap (baseChangeIso n b).hom := by
  ext T x
  change pointsEquiv n R _ (baseChangePointsEquiv b _ T x) ∈ blockParabolicSubgroup _ e ↔
    pointsEquiv n R' T (x ≫ _) ∈ blockParabolicSubgroup _ e
  rw [pointsEquiv_comp_baseChangeIso_hom]
  rfl

/-- The block Levi subgroup functor commutes with base change. -/
theorem blockLevi_baseChange :
    (blockLevi n R e).baseChange b = (blockLevi n R' e).comap (baseChangeIso n b).hom := by
  ext T x
  change pointsEquiv n R _ (baseChangePointsEquiv b _ T x) ∈ blockLeviSubgroup _ e ↔
    pointsEquiv n R' T (x ≫ _) ∈ blockLeviSubgroup _ e
  rw [pointsEquiv_comp_baseChangeIso_hom]
  rfl

/-- The block unipotent subgroup functor commutes with base change. -/
theorem blockUnipotent_baseChange :
    (blockUnipotent n R e).baseChange b =
      (blockUnipotent n R' e).comap (baseChangeIso n b).hom := by
  ext T x
  change pointsEquiv n R _ (baseChangePointsEquiv b _ T x) ∈ blockUnipotentSubgroup _ e ↔
    pointsEquiv n R' T (x ≫ _) ∈ blockUnipotentSubgroup _ e
  rw [pointsEquiv_comp_baseChangeIso_hom]
  rfl

/-- `P(λ)` of the diagonal cocharacter commutes with base change. -/
theorem parabolic_diagonalCocharacter_baseChange :
    (Dynamic.parabolic (diagonalCocharacter n R e)).baseChange b =
      (Dynamic.parabolic (diagonalCocharacter n R' e)).comap (baseChangeIso n b).hom := by
  rw [← Dynamic.parabolic_baseChange, Dynamic.parabolic_eq_comap_of_iso _ (baseChangeIso n b),
    baseChangeCocharacter_diagonalCocharacter]

/-- `Z(λ)` of the diagonal cocharacter commutes with base change. -/
theorem centralizer_diagonalCocharacter_baseChange :
    (Dynamic.centralizer (diagonalCocharacter n R e)).baseChange b =
      (Dynamic.centralizer (diagonalCocharacter n R' e)).comap (baseChangeIso n b).hom := by
  rw [← Dynamic.centralizer_baseChange,
    Dynamic.centralizer_eq_comap_of_iso _ (baseChangeIso n b),
    baseChangeCocharacter_diagonalCocharacter]

/-- `U(λ)` of the diagonal cocharacter commutes with base change. -/
theorem unipotent_diagonalCocharacter_baseChange :
    (Dynamic.unipotent (diagonalCocharacter n R e)).baseChange b =
      (Dynamic.unipotent (diagonalCocharacter n R' e)).comap (baseChangeIso n b).hom := by
  rw [← Dynamic.unipotent_baseChange, Dynamic.unipotent_eq_comap_of_iso _ (baseChangeIso n b),
    baseChangeCocharacter_diagonalCocharacter]

end Langlands.GroupScheme.GeneralLinear
