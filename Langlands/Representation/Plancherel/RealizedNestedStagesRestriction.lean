import Langlands.Representation.Plancherel.RealizedNestedIntegral
import Langlands.Representation.Aubert.General.InductionCarrierTransport

/-! # Actual stages restriction through the represented Levi -/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviContinuation DynamicOppositeCanonicalScalar
open QuotientIntegration

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G L : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
  (o : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (j : L ⟶ G) (hj : (Dynamic.centralizer o).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
  (x : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (a : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hx : Dynamic.parabolic x = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic a) ∧
    Dynamic.centralizer x = (Dynamic.centralizer a).map j ∧
    Dynamic.unipotent x = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent a))
  (hG : IsConnectedReductive G) (hL : IsConnectedReductive L)

local notation "pt" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "XG" => rationalPoints G
local notation "XL" => rationalPoints L
local notation "e" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
local notation "incl" => Dynamic.realized_centralizer_le o j hj a x hx.2.1 pt
local notation "eL" => RealizedLeviTransport.centralizerEquiv F o j hj hjc a x hx
local notation "eSub" => subgroupOfContinuousEquiv incl

/-- The inner common Levi is identified with the ambient one by the exact
represented rational point inclusion. -/
def realizedLeviEquiv : levi a ≃ₜ* levi x := (eL).trans eSub

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom] in
@[simp]
theorem realizedLeviEquiv_coe (l : levi a) :
    (realizedLeviEquiv o j hj hjc x a hx l : XG) = (e (l : XL) : XG) :=
  (subgroupOfContinuousEquiv_apply incl (eL l)).trans
    (congrArg (Subtype.val : levi o → XG) (GroupTransport.subgroupEquiv_apply e
      (RealizedLeviTransport.centralizer_mem F o j hj hjc a x hx) l))

local notation "eM" => realizedLeviEquiv o j hj hjc x a hx
local notation "I" => fun A => (DynamicNormalization.leviTwistedInductionFunctor
  (decomposition x) (radical_isClosed x)).obj A
local notation "J" => fun B => (DynamicNormalization.leviTwistedInductionFunctor
  (decomposition a) (radical_isClosed a)).obj B

variable (A : SmoothRep.{0, u, uV} ℂ (levi x))

local notation "As" => SmoothRep.pullback eM A
local notation "An" => SmoothRep.pullback eL (SmoothRep.pullback eSub A)
local notation "Uδ" => radical_unimodular x hG
local notation "Lδ" => radical_unimodular a hL
local notation "E₀" => normalizedInductionLeviEquiv (decomposition x) (radical_isClosed x) Uδ A
local notation "E₁" => normalizedInductionLeviEquiv (decomposition a) (radical_isClosed a) Lδ As
local notation "Stages" => (RealizedLeviStages.inductionInStagesIso F hG o j hj hjc a x hx
  (radical_isClosed x) (radical_isClosed o) (levi_isClosed o)).app A
local notation "Bl" => (normalizedInductionFunctor (decomposition a) (radical_isClosed a)).obj An
local notation "Bg" => SmoothRep.pullback (e).symm Bl

private def realizedCoefficientEquiv : (An).representation.Equiv (As).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ A) (fun _ => rfl)

local notation "E₂" => normalizedInductionEquivOfEquiv
  (decomposition a) (radical_isClosed a) (realizedCoefficientEquiv o j hj hjc x a hx A)

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluate the actual induction-in-stages isomorphism in the outer variable
and transport from the normalized models to the Levi-inflated models. -/
def realizedStagesRestriction (g : XG) : I A →ₗ[ℂ] J As := by
  let S := SmoothRep.equivOfIso Stages
  let ev : ((normalizedInductionFunctor (decomposition o) (radical_isClosed o)).obj Bg) →ₗ[ℂ] Bl :=
    { toFun := fun f => eval (parabolic o) (inducingRepresentation (decomposition o) (radical_isClosed o) Bg) f g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (E₁).toLinearEquiv.toLinearMap.comp ((E₂).toLinearEquiv.toLinearMap.comp
    (ev.comp (S.toLinearEquiv.toLinearMap.comp (E₀).symm.toLinearEquiv.toLinearMap)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The stages map literally removes the outer half modulus from the
restricted section at the specified argument. -/
theorem realizedStagesRestriction_formula (f : I A) (g : XG) :
    RealizedRestrictionFormula o j hj hjc x a (decomposition x) (decomposition a) A eM f g
      (realizedStagesRestriction o j hj hjc x a hx hG hL A g f) := by
  intro l
  exact RealizedLeviStages.inductionInStagesIso_hom_eval F hG o j hj hjc a x hx
    (radical_isClosed x) (radical_isClosed o) (levi_isClosed o) A ((E₀).symm f) g l

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual restriction at the outer identity is surjective. -/
theorem realizedStagesRestriction_surjective : Function.Surjective
    (realizedStagesRestriction o j hj hjc x a hx hG hL A 1) := by
  intro v
  let S := SmoothRep.equivOfIso Stages
  let vl := (E₂).symm ((E₁).symm v)
  obtain ⟨F₁, hF₁⟩ := normalizedInduction_eval_surjective (decomposition o)
    (radical_isClosed o) (projection_continuous o) Bg vl
  refine ⟨E₀ (S.symm F₁), ?_⟩
  change E₁ (E₂ (eval (parabolic o) (inducingRepresentation (decomposition o) (radical_isClosed o) Bg)
    (S ((E₀).symm (E₀ (S.symm F₁)))) 1)) = v
  rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.apply_symm_apply]
  exact (congrArg (fun f : Bl => E₁ (E₂ f)) hF₁).trans
    ((congrArg (E₁) ((E₂).apply_symm_apply ((E₁).symm v))).trans ((E₁).apply_symm_apply v))

section Aligned

variable {M : Subgroup XG} {M' : Subgroup XL}
  (hM : levi x = M) (hM' : levi a = M')
  (B : SmoothRep.{0, u, uV} ℂ M)
  (eC : M' ≃ₜ* M) (heC : ∀ l, (eC l : XG) = (e (l : XL) : XG))
  (dG : IsSemidirectDecomposition (parabolic x) M (radical x))
  (dL : IsSemidirectDecomposition (parabolic a) M' (radical a))

local notation "JCG" => (DynamicNormalization.leviTwistedInductionFunctor dG (radical_isClosed x)).obj B
local notation "JCL" => (DynamicNormalization.leviTwistedInductionFunctor dL (radical_isClosed a)).obj
  (SmoothRep.pullback eC B)

include hM hM' heC hx hG hL in
set_option backward.isDefEq.respectTransparency.types false in
/-- The surjective realized stages restriction can use any given presentations
of the same literal inducing subgroups and the same exact point embedding. -/
theorem exists_realizedStagesRestriction_aligned :
    ∃ R : JCG →ₗ[ℂ] JCL, Function.Surjective R ∧
      ∀ f, RealizedRestrictionFormula o j hj hjc x a dG dL B eC f 1 (R f) := by
  subst M
  subst M'
  have he : eC = eM := by
    apply DFunLike.ext
    intro l
    exact Subtype.ext ((heC l).trans (realizedLeviEquiv_coe o j hj hjc x a hx l).symm)
  subst eC
  refine ⟨realizedStagesRestriction o j hj hjc x a hx hG hL B 1,
    realizedStagesRestriction_surjective o j hj hjc x a hx hG hL B, ?_⟩
  intro f
  exact realizedStagesRestriction_formula o j hj hjc x a hx hG hL B f 1

end Aligned

end Langlands.Plancherel.StandardIntertwining
