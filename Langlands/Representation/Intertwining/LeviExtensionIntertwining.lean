import Langlands.Representation.Exponents.LeviInductionStages
import Langlands.Representation.Intertwining.InnerLeviIntegrationDomain
import Langlands.Representation.Intertwining.InnerLeviRegularity
import Langlands.Representation.Intertwining.InnerLeviOperatorIdentity
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic

/-! # Integral intertwining for parabolic extensions -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace LeviParabolicExtensionDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  {G L M P U Q₁ N₁ Q₂ N₂ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom] [IsAffineHom M.X.hom]

local instance extensionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

local instance extensionIntermediatePointTopology : TopologicalSpace (rationalPoints L) :=
  RationalPointFamily.pointTopology

local instance extensionLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints L)] [NonarchimedeanGroup (rationalPoints L)]
  (hG : IsConnectedReductive G)
  {p : P ⟶ G} {l : L ⟶ P} (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {q₁ : Q₁ ⟶ L} {m₁ : M ⟶ Q₁} (n₁ : N₁ ⟶ Q₁)
  (hq₁ : IsParabolicSubgroup q₁) (hm₁ : IsRationalLeviSubgroup m₁)
  (hn₁ : LeviSubgroup.IsGeometricUnipotentRadical n₁)
  (hmul₁ : IsIso (subgroupMultiplication m₁ n₁))
  (D₁ : LeviParabolicExtensionDatum p l q₁ m₁)

local notation "upper₁" => leviInductionFunctor D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hrR D₁.hnR D₁.hmulR
local notation "lower₁" => leviInductionFunctor q₁ m₁ n₁ hq₁ hn₁ hm₁ hmul₁

/-- The stage restriction along the intermediate Levi, with its half modulus. -/
abbrev stageRestriction (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M)) :
    (upper₁).obj σ →ₗ[ℂ] (lower₁).obj σ :=
  innerStageRestriction hG D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    p l r hp hl hr hmul D₁.pointImage_le q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁
    D₁.levi_comp.symm (D₁.pointImage_inf.trans (inf_comm _ _)) σ

/-- The restriction fixes evaluation at the identity. -/
theorem stageRestriction_eval_one
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M)) (f : (upper₁).obj σ) :
    Induction.eval _ _ (stageRestriction hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ f) 1 =
      Induction.eval _ _ f 1 := by
  have he := innerStageRestriction_eval hG D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    p l r hp hl hr hmul D₁.pointImage_le q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁
    D₁.levi_comp.symm (D₁.pointImage_inf.trans (inf_comm _ _)) σ f 1
  rw [map_one, Units.val_one, inv_one, one_smul, map_one] at he
  exact he

/-- Every lower section is the stage restriction of an upper section. -/
theorem stageRestriction_surjective (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M)) :
    Function.Surjective (stageRestriction hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ) :=
  innerStageRestriction_surjective hG D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    p l r hp hl hr hmul D₁.pointImage_le q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁
    D₁.levi_comp.symm (D₁.pointImage_inf.trans (inf_comm _ _)) σ

set_option maxHeartbeats 600000 in
/-- An equivariant endomorphism commuting with stage restriction is the same
scalar as the lower endomorphism. To detect the upper map, evaluate the
restriction of every right translate at one. -/
theorem stageRestriction_scalar_iff (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M))
    (J : ((upper₁).obj σ).representation.IntertwiningMap ((upper₁).obj σ).representation)
    (J' : ((lower₁).obj σ).representation.IntertwiningMap ((lower₁).obj σ).representation)
    (hJ : ∀ f, stageRestriction hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ (J f) =
      J' (stageRestriction hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ f)) (c : ℂ) :
    (∀ f, J f = c • f) ↔ (∀ f, J' f = c • f) := by
  let T := stageRestriction hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ
  let ε₁ := fun f : (upper₁).obj σ => Induction.eval _ _ f (1 : rationalPoints G)
  let ε₂ := fun f : (lower₁).obj σ => Induction.eval _ _ f (1 : rationalPoints L)
  have hT (f : (upper₁).obj σ) : ε₂ (T f) = ε₁ f :=
    stageRestriction_eval_one hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ f
  constructor
  · intro h φ
    obtain ⟨f, rfl⟩ := stageRestriction_surjective hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ φ
    exact (hJ f).symm.trans ((congrArg T (h f)).trans (map_smul T c f))
  · intro h f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    let ρ := ((upper₁).obj σ).representation
    have hstep : T (J (ρ g f)) = T (c • ρ g f) :=
      (hJ _).trans ((h _).trans (map_smul T c (ρ g f)).symm)
    have hleft : J (ρ g f) = ρ g (J f) :=
      Representation.IntertwiningMap.isIntertwining _ _ J g f
    have hright : c • ρ g f = ρ g (c • f) := (map_smul (ρ g) c f).symm
    have hg := (congrArg ε₁ hleft).symm.trans
      ((hT _).symm.trans ((congrArg ε₂ hstep).trans ((hT _).trans (congrArg ε₁ hright))))
    change Induction.eval _ _ (J f) (1 * g) = Induction.eval _ _ (c • f) (1 * g) at hg
    rw [one_mul] at hg
    exact hg

section Pair

variable {q₂ : Q₂ ⟶ L} {m₂ : M ⟶ Q₂} (n₂ : N₂ ⟶ Q₂)
  (hq₂ : IsParabolicSubgroup q₂) (hm₂ : IsRationalLeviSubgroup m₂)
  (hn₂ : LeviSubgroup.IsGeometricUnipotentRadical n₂)
  (hmul₂ : IsIso (subgroupMultiplication m₂ n₂))
  (D₂ : LeviParabolicExtensionDatum p l q₂ m₂)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (a : A.toGrp ⟶ M)

local notation "upper₂" => leviInductionFunctor D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hrR D₂.hnR D₂.hmulR
local notation "lower₂" => leviInductionFunctor q₂ m₂ n₂ hq₂ hn₂ hm₂ hmul₂
local notation "regularUpper" =>
  IsPQRegular D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hrR D₁.hnR D₁.hmulR
    D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hrR D₂.hnR D₂.hmulR a
local notation "regularLower" =>
  IsPQRegular q₁ m₁ n₁ hq₁ hn₁ hm₁ hmul₁ q₂ m₂ n₂ hq₂ hn₂ hm₂ hmul₂ a

include hG r hp hl hr hmul in
set_option maxHeartbeats 600000 in
/-- Regularity descends from the parabolic extensions to the inner pair. -/
theorem lower_isPQRegular (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M))
    (hσ : regularUpper σ) : regularLower σ :=
  innerLevi_isPQRegular hG D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hnR D₂.hrR D₂.hmulR p l r hp hl hr hmul
    D₁.pointImage_le D₂.pointImage_le q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁ q₂ m₂ n₂ hq₂ hm₂ hn₂ hmul₂
    D₁.levi_comp.symm D₂.levi_comp.symm (D₁.pointImage_inf.trans (inf_comm _ _))
    (D₂.pointImage_inf.trans (inf_comm _ _)) a σ hσ

include hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ hq₂ hm₂ hn₂ hmul₂ in
omit [IsAffineHom M.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [LocallyCompactSpace (rationalPoints L)]
  [NonarchimedeanGroup (rationalPoints L)] in
set_option maxHeartbeats 600000 in
/-- If the two inner parabolics are opposite, the inclusion of their wall Levi
identifies the inner integration complement with the upper complement. -/
theorem exists_innerComplementEquiv
    (B : OppositeLeviParabolicData D₁.pR D₁.nR)
    (hM : m₂ ≫ q₂ = m₁ ≫ q₁)
    (hOpp : pointImage q₁ ⊓ pointImage q₂ = pointImage (m₁ ≫ q₁)) :
    let V := pointImage (B.unipotent ≫ B.inclusion) ⊓ pointImage (D₂.rR ≫ D₂.pR)
    let V' := pointImage (n₂ ≫ q₂) ⊓ pointImage (n₂ ≫ q₂)
    ∃ e : V' ≃ₜ* V, ∀ x : V', (e x : rationalPoints G) = rationalPoints.map (l ≫ p) x := by
  have hM' : D₂.nR ≫ D₂.pR = D₁.nR ≫ D₁.pR := by
    rw [D₂.levi_comp, D₁.levi_comp, ← Category.assoc m₂, hM, Category.assoc]
  have hV := innerIntegrationDomain_eq_map hG D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hnR D₂.hrR D₂.hmulR B.isParabolic B.isLevi B.isRadical
    p l r hp hl hr hmul hM' B.levi_comp B.intersection D₁.pointImage_le D₂.pointImage_le
    q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁ q₂ m₂ n₂ hq₂ hm₂ hn₂ hmul₂ hq₂ hm₂ hn₂
    D₁.levi_comp.symm hM hM hOpp (D₁.pointImage_inf.trans (inf_comm _ _))
    (D₂.pointImage_inf.trans (inf_comm _ _))
  exact exists_leviSubgroupEquiv p l hp hl _ _ hV

set_option maxHeartbeats 1000000 in
/-- Integral-normalized maps at compatible measures commute with the stage restrictions. -/
theorem stageRestriction_intertwiner (ha : IsSplitComponent a)
    (V : Subgroup (rationalPoints G)) (V' : Subgroup (rationalPoints L))
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace V'] [BorelSpace V']
    (hV' : V' ≤ pointImage (n₂ ≫ q₂))
    (e : V' ≃ₜ* V) (he : ∀ x : V', (e x : rationalPoints G) = rationalPoints.map (l ≫ p) x)
    (measure' : Measure V') (measure : Measure V) (hmeasure : measure = measure'.map e)
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints M)) (hσ : regularUpper σ)
    (J : ((upper₁).obj σ).representation.IntertwiningMap ((upper₂).obj σ).representation)
    (J' : ((lower₁).obj σ).representation.IntertwiningMap ((lower₂).obj σ).representation)
    (hJ : IsIntegralIntertwiner D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hrR D₁.hnR D₁.hmulR
      D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hrR D₂.hnR D₂.hmulR V measure σ J)
    (hJ' : IsIntegralIntertwiner q₁ m₁ n₁ hq₁ hn₁ hm₁ hmul₁ q₂ m₂ n₂ hq₂ hn₂ hm₂ hmul₂
      V' measure' σ J')
    (f : (upper₁).obj σ) :
    stageRestriction hG r hp hl hr hmul n₂ hq₂ hm₂ hn₂ hmul₂ D₂ σ (J f) =
      J' (stageRestriction hG r hp hl hr hmul n₁ hq₁ hm₁ hn₁ hmul₁ D₁ σ f) := by
  let ψ₁ := leviInductionStagesIso D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    p l r hp hl hr hmul q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁
    D₁.pointImage_le D₁.levi_comp.symm D₁.pointImage_inf hG
  have hF := leviInductionStagesIso_eval' D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    p l r hp hl hr hmul q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁
    D₁.pointImage_le D₁.levi_comp.symm D₁.pointImage_inf hG σ f
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h := innerLevi_integralIntertwiner_formula hG D₁.pR D₁.nR D₁.rR D₁.hpR D₁.hnR D₁.hrR D₁.hmulR
    D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hnR D₂.hrR D₂.hmulR p l r hp hl hr hmul
    D₁.pointImage_le D₂.pointImage_le q₁ m₁ n₁ hq₁ hm₁ hn₁ hmul₁ q₂ m₂ n₂ hq₂ hm₂ hn₂ hmul₂
    D₁.levi_comp.symm D₂.levi_comp.symm (D₁.pointImage_inf.trans (inf_comm _ _))
    (D₂.pointImage_inf.trans (inf_comm _ _)) a ha V V' hV' e he measure' measure hmeasure
    σ hσ J J' hJ hJ' f (SmoothRep.hom (ψ₁.hom.app σ) f) hF 1 x
  rw [mul_one] at h
  exact (innerStageRestriction_eval hG D₂.pR D₂.nR D₂.rR D₂.hpR D₂.hnR D₂.hrR D₂.hmulR
    p l r hp hl hr hmul D₂.pointImage_le q₂ m₂ n₂ hq₂ hm₂ hn₂ hmul₂
    D₂.levi_comp.symm (D₂.pointImage_inf.trans (inf_comm _ _)) σ (J f) x).trans h.symm

end Pair

end LeviParabolicExtensionDatum

end Langlands.Aubert.General.RepresentedParabolic
