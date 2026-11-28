import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.RelativeLevi.LeviCoverDescent
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Base change of the `GL_n` block subgroup schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {R R' : CommRingCat.{u}}
  (b : Spec R' ⟶ Spec R) (e : n → ℤ)

private theorem isRepresentedBy_comp_baseChangeIso {H : GroupScheme (Spec R)}
    {i : H ⟶ groupScheme n R} {F : SubgroupFunctor (groupScheme n R)}
    {F' : SubgroupFunctor (groupScheme n R')} (h : F.IsRepresentedBy i)
    (hF : F.baseChange b = F'.comap (baseChangeIso n b).hom) :
    F'.IsRepresentedBy ((GroupScheme.baseChange b).map i ≫ (baseChangeIso n b).hom) := by
  refine ⟨?_, ?_⟩
  · let : Mono ((GroupScheme.baseChange b).map i).hom.hom := (h.baseChange b).1
    let : IsIso (baseChangeIso n b).hom.hom.hom :=
      inferInstanceAs (IsIso ((Grp.forget (Over (Spec R'))).mapIso (baseChangeIso n b)).hom)
    rw [Grp.comp_hom_hom]
    infer_instance
  · rw [SubgroupFunctor.range_comp_iso, (h.baseChange b).2, hF,
      ← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id]

/-- The pulled-back block parabolic is the block parabolic over the new ring. -/
def blockParabolicBaseChangeIso :
    (GroupScheme.baseChange b).obj (blockParabolicScheme n R e) ≅ blockParabolicScheme n R' e :=
  (isRepresentedBy_comp_baseChangeIso b (isRepresentedBy_blockParabolic n R e)
    (blockParabolic_baseChange b e)).isoOfIsRepresentedBy (isRepresentedBy_blockParabolic n R' e)

/-- The pulled-back block Levi is the block Levi over the new ring. -/
def blockLeviBaseChangeIso :
    (GroupScheme.baseChange b).obj (blockLeviScheme n R e) ≅ blockLeviScheme n R' e :=
  (isRepresentedBy_comp_baseChangeIso b (isRepresentedBy_blockLevi n R e)
    (blockLevi_baseChange b e)).isoOfIsRepresentedBy (isRepresentedBy_blockLevi n R' e)

/-- The pulled-back block unipotent group is the block unipotent group over the new ring. -/
def blockUnipotentBaseChangeIso :
    (GroupScheme.baseChange b).obj (blockUnipotentScheme n R e) ≅ blockUnipotentScheme n R' e :=
  (isRepresentedBy_comp_baseChangeIso b (isRepresentedBy_blockUnipotent n R e)
    (blockUnipotent_baseChange b e)).isoOfIsRepresentedBy (isRepresentedBy_blockUnipotent n R' e)

@[reassoc]
theorem blockParabolicBaseChangeIso_hom_comp :
    (blockParabolicBaseChangeIso b e).hom ≫ blockParabolicHom n R' e =
      (GroupScheme.baseChange b).map (blockParabolicHom n R e) ≫ (baseChangeIso n b).hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[reassoc]
theorem blockLeviBaseChangeIso_hom_comp :
    (blockLeviBaseChangeIso b e).hom ≫ blockLeviHom n R' e =
      (GroupScheme.baseChange b).map (blockLeviHom n R e) ≫ (baseChangeIso n b).hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[reassoc]
theorem blockUnipotentBaseChangeIso_hom_comp :
    (blockUnipotentBaseChangeIso b e).hom ≫ blockUnipotentHom n R' e =
      (GroupScheme.baseChange b).map (blockUnipotentHom n R e) ≫ (baseChangeIso n b).hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The block limit homomorphism commutes with the model comparisons. -/
theorem blockLimitHom_baseChange :
    (GroupScheme.baseChange b).map (blockLimitHom n R e) ≫ (blockLeviBaseChangeIso b e).hom =
      (blockParabolicBaseChangeIso b e).hom ≫ blockLimitHom n R' e := by
  apply (isRepresentedBy_blockLevi n R' e).hom_ext
  rw [Category.assoc, blockLeviBaseChangeIso_hom_comp]
  refine hom_ext_points fun T p => (pointsEquiv n R' T).injective ?_
  let p₀ := baseChangePointsEquiv b (blockParabolicScheme n R e) T p
  let p₁ := p ≫ (blockParabolicBaseChangeIso b e).hom.hom.hom
  have hp :
      pointsEquiv n R ((Over.map b).obj T) (p₀ ≫ (blockParabolicHom n R e).hom.hom) =
        pointsEquiv n R' T (p₁ ≫ (blockParabolicHom n R' e).hom.hom) := by
    have hi := congrArg (fun f => f.hom.hom) (blockParabolicBaseChangeIso_hom_comp b e)
    simp only [Grp.comp_hom_hom] at hi
    dsimp only [p₀, p₁]
    rw [Category.assoc, hi, ← Category.assoc, pointsEquiv_comp_baseChangeIso_hom,
      baseChangePointsEquiv_comp]
  have h₀ := pointsEquiv_blockLimitHom n R e p₀
  have h₁ := pointsEquiv_blockLimitHom n R' e p₁
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp, baseChangePointsEquiv_comp]
  exact h₀.trans ((congrArg (blockLeviProjection Γ(T.left, ⊤) e) (Subtype.ext hp)).trans h₁.symm)

/-- The inclusion of the block Levi into the parabolic commutes with the model comparisons. -/
theorem blockLeviToParabolic_baseChange :
    (GroupScheme.baseChange b).map (blockLeviToParabolic n R e) ≫
        (blockParabolicBaseChangeIso b e).hom =
      (blockLeviBaseChangeIso b e).hom ≫ blockLeviToParabolic n R' e := by
  apply (isRepresentedBy_blockParabolic n R' e).hom_ext
  rw [Category.assoc, blockParabolicBaseChangeIso_hom_comp, ← Category.assoc,
    ← Functor.map_comp, blockLeviToParabolic_comp, Category.assoc, blockLeviToParabolic_comp,
    blockLeviBaseChangeIso_hom_comp]

/-- The inclusion of the block unipotent subgroup through the kernel of the block limit
commutes with the model comparisons. -/
theorem blockUnipotentIsoKernel_inclusion_baseChange :
    let inclusion := fun A : CommRingCat.{u} =>
      (blockUnipotentIsoKernel n A e).hom ≫ kernelι (blockLimitHom n A e)
    (GroupScheme.baseChange b).map (inclusion R) ≫ (blockParabolicBaseChangeIso b e).hom =
      (blockUnipotentBaseChangeIso b e).hom ≫ inclusion R' := by
  dsimp only
  apply (isRepresentedBy_blockParabolic n R' e).hom_ext
  rw [Category.assoc, blockParabolicBaseChangeIso_hom_comp, ← Category.assoc,
    ← Functor.map_comp, Category.assoc, blockUnipotentIsoKernel_hom_comp,
    Category.assoc, Category.assoc, blockUnipotentIsoKernel_hom_comp,
    blockUnipotentBaseChangeIso_hom_comp]

/-- Multiplication of the block factors commutes with base change and the model comparisons. -/
theorem blockMultiplicationIso_hom_baseChange :
    Functor.LaxMonoidal.μ (Over.pullback b)
        (blockUnipotentScheme n R e).X (blockLeviScheme n R e).X ≫
      (Over.pullback b).map (blockMultiplicationIso n R e).hom ≫
      (blockParabolicBaseChangeIso b e).hom.hom.hom =
    ((blockUnipotentBaseChangeIso b e).hom.hom.hom ⊗ₘ (blockLeviBaseChangeIso b e).hom.hom.hom) ≫
      (blockMultiplicationIso n R' e).hom := by
  let F := Over.pullback b
  let B := GroupScheme.baseChange b
  let p := blockParabolicHom n R e
  let u := blockUnipotentHom n R e
  let z := blockLeviHom n R e
  let p' := blockParabolicHom n R' e
  let u' := blockUnipotentHom n R' e
  let z' := blockLeviHom n R' e
  let g := (baseChangeIso n b).hom
  let pOver : F.obj (blockParabolicScheme n R e).X ⟶ (blockParabolicScheme n R' e).X :=
    (blockParabolicBaseChangeIso b e).hom.hom.hom
  let uOver : F.obj (blockUnipotentScheme n R e).X ⟶ (blockUnipotentScheme n R' e).X :=
    (blockUnipotentBaseChangeIso b e).hom.hom.hom
  let zOver : F.obj (blockLeviScheme n R e).X ⟶ (blockLeviScheme n R' e).X :=
    (blockLeviBaseChangeIso b e).hom.hom.hom
  let gOver : F.obj (groupScheme n R).X ⟶ (groupScheme n R').X := g.hom.hom
  have hp : pOver ≫ p'.hom.hom = F.map p.hom.hom ≫ gOver :=
    congrArg (fun f => f.hom.hom) (blockParabolicBaseChangeIso_hom_comp b e)
  have hPullback : F.map (blockMultiplicationIso n R e).hom ≫ F.map p.hom.hom =
      F.map (subgroupMultiplication u z) := by
    rw [← F.map_comp, blockMultiplicationIso_hom_comp]
    rfl
  have hFactors :
      (uOver ⊗ₘ zOver) ≫ subgroupMultiplication u' z' =
        subgroupMultiplication (B.map u ≫ g) (B.map z ≫ g) :=
    RelativeLevi.subgroupMultiplication_comp _ _ _ _ _ _
      (blockUnipotentBaseChangeIso_hom_comp b e) (blockLeviBaseChangeIso_hom_comp b e)
  have hTarget : (blockMultiplicationIso n R' e).hom ≫ p'.hom.hom =
      subgroupMultiplication u' z' :=
    blockMultiplicationIso_hom_comp n R' e
  apply (isRepresentedBy_blockParabolic n R' e).1.right_cancellation
  change (Functor.LaxMonoidal.μ F (blockUnipotentScheme n R e).X (blockLeviScheme n R e).X ≫
      F.map (blockMultiplicationIso n R e).hom ≫ pOver) ≫ p'.hom.hom =
    ((uOver ⊗ₘ zOver) ≫ (blockMultiplicationIso n R' e).hom) ≫ p'.hom.hom
  simp only [Category.assoc, hp, reassoc_of% hPullback, hTarget, hFactors]
  rw [← Category.assoc, RelativeLevi.subgroupMultiplication_baseChange,
    subgroupMultiplication_postcomp]
  rfl

end Langlands.GroupScheme.GeneralLinear
