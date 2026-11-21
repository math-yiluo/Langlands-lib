import Langlands.Automorphic.GeneralLinearQuotientFormClassClosure
import Langlands.Automorphic.OperatorJointVectorRecovery
import Langlands.Representation.Archimedean.HilbertSubmoduleAction

/-! # Joint-vector recovery for represented forms on the original positive quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup R.toSubmodule

/-- If the class image of a represented operator realization lies in the closure of a jointly
admissible one's class image, then it lies in the latter's algebraic class image itself. All
split-centre and Haar hypotheses are binders of the proposition. -/
def GeneralLinearQuotientJointRecoveryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (_hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (_e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (_hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
    (R₁ R₂ : OperatorRealization F (r + 1)), R₁.IsJointlyAdmissible →
    ∀ (j₁ : R₁.Space →ₗ[ℂ] Lp ℂ 2 (positiveRationalQuotientHaarMeasure F
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i))
      (j₂ : R₂.Space →ₗ[ℂ] Lp ℂ 2 (positiveRationalQuotientHaarMeasure F
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) T i)),
      (∀ f, IsGeneralLinearFormClass F r T i (j₁ f) (R₁.toContinuous f)) →
      (∀ f, IsGeneralLinearFormClass F r T i (j₂ f) (R₂.toContinuous f)) →
      LinearMap.range j₂ ≤ (LinearMap.range j₁).topologicalClosure →
        LinearMap.range j₂ ≤ LinearMap.range j₁

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "n" => r + 1
local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
local notation "E" => Lp ℂ 2 μQ
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F n

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
private def matrixFiniteInclusion : FiniteAdelicGL F n →* AdelicGroupPoints F GLs :=
  (m).symm.toMulEquiv.toMonoidHom.comp (AdelicGL.ofFinite F n).toMonoidHom

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
private def matrixCompactInclusion : standardInfiniteCompact F n →* AdelicGroupPoints F GLs :=
  ((m).symm.toMulEquiv.toMonoidHom.comp (AdelicGL.ofInfinite F n).toMonoidHom).comp
    (standardInfiniteCompact F n).subtype

include hi I e hc in
set_option maxHeartbeats 700000 in
/-- Faithfulness in the other direction: the same measured quotient class cannot represent
two different continuous forms, since the canonical quotient Haar measure has full support. -/
theorem generalLinearFormClass_form_eq {x : E}
    {f g : Langlands.Automorphic.ContinuousRationalFunctions F n}
    (hf : IsGeneralLinearFormClass F r T i x f) (hg : IsGeneralLinearFormClass F r T i x g) : f = g := by
  let := positiveRationalQuotient_borelSpace F GLs T i hi I e hc
  let := haarQuotientMeasure_isOpenPosMeasure F GLs T i hi I e hc
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  have h : a = b := ContinuousMap.ext (congrFun
    (Measure.eq_of_ae_eq (ha'.symm.trans hb') a.continuous b.continuous))
  rw [← ha, h, hb]

private theorem quotient_inner_invariant (a : AdelicGroupPoints F GLs) (x y : E) :
    Inner.inner ℂ (ρ a x) (ρ a y) = Inner.inner ℂ x y := by
  let L : E →ₗᵢ[ℂ] E := ⟨(ρ a).toLinearMap,
    norm_haarQuotientL2BoundedRightAction F GLs T i hi I e hc a⟩
  exact L.inner_map_map x y

/-- Abstract recovery: pull the Hilbert form back to the jointly admissible carrier, recover
every finite-smooth and compact-finite vector of the completion, and apply it to the image of a
second equivariant map. -/
private theorem abstractJointRecovery
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Type*} [Group K]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ₁ : Representation ℂ G V₁} {κ₁ : Representation ℂ K V₁}
    {ρ₂ : Representation ℂ G V₂} {κ₂ : Representation ℂ K V₂}
    (σ : Representation ℂ G H) (τ : Representation ℂ K H)
    (hσ : ∀ d x y, Inner.inner ℂ (σ d x) (σ d y) = Inner.inner ℂ x y)
    (hτ : ∀ k x y, Inner.inner ℂ (τ k x) (τ k y) = Inner.inner ℂ x y)
    (a₁ : V₁ →ₗ[ℂ] H) (ha₁ : Function.Injective a₁) (hd : DenseRange a₁) (a₂ : V₂ →ₗ[ℂ] H)
    (hσ₁ : ∀ d v, a₁ (ρ₁ d v) = σ d (a₁ v)) (hτ₁ : ∀ k v, a₁ (κ₁ k v) = τ k (a₁ v))
    (hσ₂ : ∀ d v, a₂ (ρ₂ d v) = σ d (a₂ v)) (hτ₂ : ∀ k v, a₂ (κ₂ k v) = τ k (a₂ v))
    (hcomm : ∀ d k v, ρ₁ d (κ₁ k v) = κ₁ k (ρ₁ d v)) (hsmooth : Langlands.IsSmooth ρ₁)
    (hfinite : ∀ v, Langlands.FiniteVectors.IsFiniteVector κ₁ v)
    (hcofinal : ∀ L : OpenSubgroup G, ∃ L₀ : OpenSubgroup G, L₀ ≤ L ∧ IsCompact (L₀ : Set G))
    (hA : Langlands.IsJointlyAdmissible ρ₁ κ₁) (hsmooth₂ : Langlands.IsSmooth ρ₂)
    (hfinite₂ : ∀ v, Langlands.FiniteVectors.IsFiniteVector κ₂ v) (v : V₂) :
    ∃ w : V₁, a₁ w = a₂ v := by
  let J₁ : ρ₁.IntertwiningMap σ := ⟨a₁, fun d => LinearMap.ext (hσ₁ d)⟩
  let bH : Langlands.InvariantPositiveForm σ := ⟨InnerProductSpace.toCore, hσ⟩
  let b := bH.comap J₁ ha₁
  have hb : ∀ k f g, b.inner (κ₁ k f) (κ₁ k g) = b.inner f g := by
    intro k f g
    change Inner.inner ℂ (a₁ (κ₁ k f)) (a₁ (κ₁ k g)) = Inner.inner ℂ (a₁ f) (a₁ g)
    rw [hτ₁, hτ₁, hτ]
  let J₂G : ρ₂.IntertwiningMap σ := ⟨a₂, fun d => LinearMap.ext (hσ₂ d)⟩
  let J₂K : κ₂.IntertwiningMap τ := ⟨a₂, fun k => LinearMap.ext (hτ₂ k)⟩
  exact (Langlands.jointVectorRecovery_of_dense b hb hcomm hsmooth hfinite hcofinal hA σ τ hσ hτ
    a₁ hd (fun _ _ => rfl) hσ₁ hτ₁ (a₂ v)).mp
      ⟨Langlands.isSmoothVector_map J₂G (hsmooth₂ v), (hfinite₂ v).map J₂K⟩

include hi I e hc in
set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Apply the abstract joint-vector recovery to the closure of the first actual quotient
image, using the pullback of its Hilbert inner product. -/
private theorem jointRecovery_aux [CompactSpace (AdeleQuotient F)]
    (R₁ R₂ : OperatorRealization F n) (hAd : R₁.IsJointlyAdmissible)
    (j₁ : R₁.Space →ₗ[ℂ] E) (j₂ : R₂.Space →ₗ[ℂ] E)
    (hj₁ : ∀ f, IsGeneralLinearFormClass F r T i (j₁ f) (R₁.toContinuous f))
    (hj₂ : ∀ f, IsGeneralLinearFormClass F r T i (j₂ f) (R₂.toContinuous f))
    (hsub : LinearMap.range j₂ ≤ (LinearMap.range j₁).topologicalClosure) :
    LinearMap.range j₂ ≤ LinearMap.range j₁ := by
  let H := (LinearMap.range j₁).topologicalClosure
  have hst (a : AdelicGroupPoints F GLs) (x : H) : ρ a x ∈ H :=
    generalLinearQuotientFormClassClosure F r T i hi I e hc R₁ j₁ hj₁ a x x.2
  let π := Langlands.Archimedean.invariantSubmoduleRepresentation ρ H hst
  let σ := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (π.comp (matrixFiniteInclusion F r))
  let τ := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (π.comp (matrixCompactInclusion F r))
  let a₁ := Langlands.Archimedean.rangeClosureEmbedding j₁
  let a₂ := j₂.codRestrict H (fun f => hsub (LinearMap.mem_range_self _ f))
  have hn₁ : Function.Injective j₁ := by
    intro f g hfg
    apply R₁.toContinuous_injective
    have hg := hj₁ g
    rw [← hfg] at hg
    exact generalLinearFormClass_form_eq F r T i hi I e hc (hj₁ f) hg
  have hσ d (x y : H) : Inner.inner ℂ (σ d x) (σ d y) = Inner.inner ℂ x y :=
    quotient_inner_invariant F r T i hi I e hc (matrixFiniteInclusion F r d) x y
  have hτ k (x y : H) : Inner.inner ℂ (τ k x) (τ k y) = Inner.inner ℂ x y :=
    quotient_inner_invariant F r T i hi I e hc (matrixCompactInclusion F r k) x y
  have hσ₁ d f : a₁ (R₁.finiteRepresentation d f) = σ d (a₁ f) :=
    Subtype.ext (generalLinear_formClass_finiteRepresentation F r T i hi I e hc R₁ j₁ hj₁ d f)
  have hτ₁ k f : a₁ (R₁.compactRepresentation k f) = τ k (a₁ f) :=
    Subtype.ext (generalLinear_formClass_compactRepresentation F r T i hi I e hc R₁ j₁ hj₁ k f)
  have hσ₂ d f : a₂ (R₂.finiteRepresentation d f) = σ d (a₂ f) :=
    Subtype.ext (generalLinear_formClass_finiteRepresentation F r T i hi I e hc R₂ j₂ hj₂ d f)
  have hτ₂ k f : a₂ (R₂.compactRepresentation k f) = τ k (a₂ f) :=
    Subtype.ext (generalLinear_formClass_compactRepresentation F r T i hi I e hc R₂ j₂ hj₂ k f)
  rintro _ ⟨f, rfl⟩
  exact (abstractJointRecovery σ τ hσ hτ a₁
    (Langlands.Archimedean.rangeClosureEmbedding_injective j₁ hn₁)
    (Langlands.Archimedean.rangeClosureEmbedding_denseRange j₁) a₂ hσ₁ hτ₁ hσ₂ hτ₂
    R₁.finiteRepresentation_compactRepresentation R₁.finiteRepresentation_isSmooth
    R₁.compactRepresentation_isFiniteVector OperatorRealization.exists_compact_openSubgroup_le hAd
    R₂.finiteRepresentation_isSmooth R₂.compactRepresentation_isFiniteVector f).imp
      fun g hg => congrArg Subtype.val hg

/-- The proposition, from the section version above. -/
theorem generalLinearQuotientJointRecovery : GeneralLinearQuotientJointRecoveryStatement.{u} := by
  intro F _ _ _ r T i hi _ I _ e hc _ R₁ R₂ hAd j₁ j₂ hj₁ hj₂ hsub
  exact jointRecovery_aux F r T i hi I e hc R₁ R₂ hAd j₁ j₂ hj₁ hj₂ hsub

end Langlands.Automorphic.GroupSchemeFunctions
