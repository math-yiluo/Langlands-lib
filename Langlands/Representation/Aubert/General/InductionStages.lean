import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.JacquetStages
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Induction.SmoothTransitivity
import Langlands.Representation.Induction.SmoothSplitQuotient
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences

/-! # Normalized smooth induction in stages for actual subgroups -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV uW

private def pullEquiv {H K : Type uG} [Group H] [Group K]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ H V} {τ : Representation ℂ H W}
    (r : K →* H) (e : σ.Equiv τ) :
    Representation.Equiv (σ.comp r) (τ.comp r) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' k := e.isIntertwining' (r k)

section WeightedSplit

variable {H M : Type uG} [Group H] [Group M]
  [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace M] [IsTopologicalGroup M]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (r : H →* M) (hr : Continuous r) (s : M →* H) (hs : Continuous s)
  (hrs : ∀ m, r (s m) = m) (Q : Subgroup H) (hker : r.ker ≤ Q)
  (σ : Representation ℂ Q V)
  (hσ : ∀ q : Q, r (q : H) = 1 → ∀ v : V, σ q v = v)
  (χ : Induction.SmoothCharacter ℂ H)
  (χM : Induction.SmoothCharacter ℂ M)
  (hχ : χM.toMonoidHom.comp r = χ.toMonoidHom)
  (τ : Representation ℂ (Q.comap s) V)
  (hτ : Langlands.twist (χM.toMonoidHom.comp (Q.comap s).subtype) τ =
    σ.comp (s.subgroupComap Q))

private def weightedSplitEquiv :
    (Langlands.twist χ.toMonoidHom ((Induction.smoothInduced (Q.comap s) τ).comp r)).Equiv
      (Induction.smoothInduced Q σ) := by
  let e₁ := equivOfRepresentationEq (show
      Langlands.twist χ.toMonoidHom ((Induction.smoothInduced (Q.comap s) τ).comp r) =
        (Langlands.twist χM.toMonoidHom (Induction.smoothInduced (Q.comap s) τ)).comp r by
    apply MonoidHom.ext
    intro h
    apply LinearMap.ext
    intro f
    change (χ.toMonoidHom h : ℂ) • (Induction.smoothInduced (Q.comap s) τ (r h) f) =
      (χM.toMonoidHom (r h) : ℂ) • (Induction.smoothInduced (Q.comap s) τ (r h) f)
    rw [← hχ]
    rfl)
  let e₂ := pullEquiv r (Induction.smoothInductionTwistEquiv (Q.comap s) χM τ)
  let e₃ := pullEquiv r (Induction.smoothInducedEquiv (Q.comap s)
    (equivOfRepresentationEq hτ))
  let e₄ := (Induction.smoothSplitQuotientEquiv r hr s hs hrs Q hker σ hσ).symm
  exact e₁.trans (e₂.trans (e₃.trans e₄))

private theorem weightedSplitEquiv_eval
    (f : Induction.SmoothFunctions (Q.comap s) τ) (h : H) :
    Induction.eval Q σ
        (weightedSplitEquiv r hr s hs hrs Q hker σ hσ χ χM hχ τ hτ f) h =
      (χM.toMonoidHom (r h) : ℂ) • Induction.eval (Q.comap s) τ f (r h) := rfl

end WeightedSplit

section Stages

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P₀ M₀ U₀ P₁ M₁ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (hM : IsClosed (M₁ : Set G)) (hMM : M₀ ≤ M₁)
  (hL : IsSemidirectDecomposition
    (P₀.subgroupOf M₁) (M₀.subgroupOf M₁) (U₀.subgroupOf M₁))
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))

/-- The actual inner modulus, read on the ambient fine Levi. -/
def inductionStagesInnerModulus : M₀ →* NNRealˣ :=
  letI := hM.locallyCompactSpace
  (HaarModulus.closedRestrictCharacter (U₀.subgroupOf M₁)
    (hU₀.preimage continuous_subtype_val) (M₀.subgroupOf M₁)
    hL.levi_le_normalizer).comp (subgroupOfContinuousEquiv hMM).symm.toMonoidHom

variable
  (hUc₀ : Jacquet.Localization.IsLimitOfCompactSubgroups U₀)
  (hUc₁ : Jacquet.Localization.IsLimitOfCompactSubgroups U₁)
  (hLUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U₀.subgroupOf M₁))
  (hδ :
    (HaarModulus.closedRestrictCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer).comp
        (Subgroup.inclusion hMM) *
      inductionStagesInnerModulus hM hMM hL hU₀ =
    HaarModulus.closedRestrictCharacter U₀ hU₀ M₀ h₀.levi_le_normalizer)

include hUc₀ hLUc hδ in
private theorem halfCharacter_stages (q : P₀.subgroupOf M₁) :
    letI := hM.locallyCompactSpace
    HaarModulus.closedHalfCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer q *
      HaarModulus.closedHalfCharacter (U₀.subgroupOf M₁)
        (hU₀.preimage continuous_subtype_val) (P₀.subgroupOf M₁) hL.le_normalizer q =
    HaarModulus.closedHalfCharacter U₀ hU₀ P₀ h₀.le_normalizer
      (subgroupOfToAmbient P₀ M₁ q) := by
  let _ := hM.locallyCompactSpace
  let m := hL.projection q
  let u : U₀.subgroupOf M₁ :=
    ⟨(m : M₁)⁻¹ * (q : M₁), hL.projection_inv_mul_mem q⟩
  have hq : (q : M₁) = (m : M₁) * (u : M₁) := by simp [u]
  have hu : HaarModulus.closedRestrictCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer u = 1 :=
    positiveCharacter_eq_one_on_compactLimit _
      (HaarModulus.isOpen_ker_closedRestrictCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer) _ hLUc u
  have huHalf : HaarModulus.closedHalfCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer u = 1 := by
    simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter,
      Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, hu, map_one]
  rw [hq, map_mul, huHalf, mul_one,
    closedHalfCharacter_eq_comp_projection hL _
      (isUnimodularModulus_of_isLimitOfCompactSubgroups _ _ hLUc),
    MonoidHom.comp_apply,
    closedHalfCharacter_eq_comp_projection h₀ hU₀
      (isUnimodularModulus_of_isLimitOfCompactSubgroups _ _ hUc₀),
    MonoidHom.comp_apply, ← h₀.projection_subgroupOf hL q]
  have hm := DFunLike.congr_fun hδ (subgroupOfContinuousEquiv hMM m)
  change
    HaarModulus.closedRestrictCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer (m : M₁) *
      HaarModulus.closedRestrictCharacter (U₀.subgroupOf M₁)
        (hU₀.preimage continuous_subtype_val) (M₀.subgroupOf M₁) hL.levi_le_normalizer m =
    HaarModulus.closedRestrictCharacter U₀ hU₀ M₀ h₀.levi_le_normalizer
      (subgroupOfToAmbient M₀ M₁ m) at hm
  unfold HaarModulus.closedHalfCharacter Jacquet.complexCharacter Jacquet.positiveHalfCharacter
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, hm]

variable (hPP : P₀ ≤ P₁) (hUU : U₁ ≤ U₀)
  (hproj : Continuous h₁.projection)

include hUc₀ hUU in
private theorem inducingRepresentation_ker
    (A : SmoothRep.{0, uG, uV} ℂ M₀)
    (q : P₀.subgroupOf P₁) (hq : h₁.projection (q : P₁) = 1) (v : A) :
    (inducingRepresentation h₀ hU₀ A).comp
      (Subgroup.subgroupOfEquivOfLe hPP).toMonoidHom q v = v := by
  let p : P₀ := Subgroup.subgroupOfEquivOfLe hPP q
  have hp : h₀.projection p = 1 :=
    (h₀.projection_eq_one_iff p).mpr
      (hUU ((h₁.projection_eq_one_iff q).mp hq))
  have hχ : HaarModulus.closedHalfCharacter U₀ hU₀ P₀ h₀.le_normalizer p = 1 := by
    rw [closedHalfCharacter_eq_comp_projection h₀ hU₀
      (isUnimodularModulus_of_isLimitOfCompactSubgroups _ _ hUc₀),
      MonoidHom.comp_apply, hp, map_one]
  change (HaarModulus.closedHalfCharacter U₀ hU₀ P₀ h₀.le_normalizer p : ℂ) •
    A.representation (h₀.projection p) v = v
  rw [hχ, hp, map_one, Units.val_one, one_smul]
  rfl

include hUc₀ hLUc hδ in
private theorem inducingRepresentation_section
    (A : SmoothRep.{0, uG, uV} ℂ M₀) :
    letI := hM.locallyCompactSpace
    Langlands.twist
      ((inductionCharacter U₁ M₁ hU₁ h₁.levi_le_normalizer).toMonoidHom.comp
        (P₀.subgroupOf M₁).subtype)
      (inducingRepresentation hL (hU₀.preimage continuous_subtype_val)
        ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hMM)).obj A)) =
    ((inducingRepresentation h₀ hU₀ A).comp
      (Subgroup.subgroupOfEquivOfLe hPP).toMonoidHom).comp
        ((Subgroup.inclusion h₁.levi_le).subgroupComap (P₀.subgroupOf P₁)) := by
  let _ := hM.locallyCompactSpace
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro v
  change (HaarModulus.closedHalfCharacter U₁ hU₁ M₁ h₁.levi_le_normalizer q : ℂ) •
      ((HaarModulus.closedHalfCharacter (U₀.subgroupOf M₁)
          (hU₀.preimage continuous_subtype_val) (P₀.subgroupOf M₁) hL.le_normalizer q : ℂ) •
        A.representation (subgroupOfToAmbient M₀ M₁ (hL.projection q)) v) =
    (HaarModulus.closedHalfCharacter U₀ hU₀ P₀ h₀.le_normalizer
      (subgroupOfToAmbient P₀ M₁ q) : ℂ) •
        A.representation (h₀.projection (subgroupOfToAmbient P₀ M₁ q)) v
  rw [smul_smul, ← Units.val_mul,
    halfCharacter_stages h₀ h₁ hM hMM hL hU₀ hU₁ hUc₀ hLUc hδ q,
    h₀.projection_subgroupOf hL q]

/-- Normalized smooth induction in stages on the literal nested subgroups.
The positive modulus product is the sole remaining normalization input. -/
private def normalizedInductionStagesCoefficientEquiv
    (A : SmoothRep.{0, uG, uV} ℂ M₀) :
    (inducingRepresentation h₁ hU₁
      ((leviNormalizedInductionFunctor.{uG, uV} hM hMM hL hU₀).obj A)).Equiv
      (Induction.smoothInduced (P₀.subgroupOf P₁)
        ((inducingRepresentation h₀ hU₀ A).comp
          (Subgroup.subgroupOfEquivOfLe hPP).toMonoidHom)) := by
  letI := hM.locallyCompactSpace
  let σ := (inducingRepresentation h₀ hU₀ A).comp
    (Subgroup.subgroupOfEquivOfLe hPP).toMonoidHom
  let τ := inducingRepresentation hL (hU₀.preimage continuous_subtype_val)
    ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hMM)).obj A)
  have hker : h₁.projection.ker ≤ P₀.subgroupOf P₁ := by
    intro p hp
    exact h₀.unipotent_le (hUU ((h₁.projection_eq_one_iff p).mp hp))
  exact weightedSplitEquiv h₁.projection hproj (Subgroup.inclusion h₁.levi_le)
    (continuous_subtype_val.subtype_mk _) h₁.projection_levi
    (P₀.subgroupOf P₁) hker σ
    (inducingRepresentation_ker h₀ h₁ hU₀ hUc₀ hPP hUU A)
    (inductionCharacter U₁ P₁ hU₁ h₁.le_normalizer)
    (inductionCharacter U₁ M₁ hU₁ h₁.levi_le_normalizer)
    (closedHalfCharacter_eq_comp_projection h₁ hU₁
      (isUnimodularModulus_of_isLimitOfCompactSubgroups _ _ hUc₁)).symm τ
    (inducingRepresentation_section h₀ h₁ hM hMM hL hU₀ hU₁ hUc₀ hLUc hδ hPP A)

/-- Evaluation at the inner identity identifies normalized smooth induction
in stages with direct normalized induction. -/
def normalizedInductionStagesEquiv (A : SmoothRep.{0, uG, uV} ℂ M₀) :=
  letI := hM.locallyCompactSpace
  (Induction.smoothInducedEquiv P₁
    (normalizedInductionStagesCoefficientEquiv h₀ h₁ hM hMM hL hU₀ hU₁
      hUc₀ hUc₁ hLUc hδ hPP hUU hproj A)).trans
    (Induction.smoothStagesEquiv P₀ P₁ hPP (inducingRepresentation h₀ hU₀ A))

/-- The stages comparison as an isomorphism of the literal functor objects. -/
def normalizedInductionStagesAppIso (A : SmoothRep.{0, uG, uV} ℂ M₀) :
    ((leviNormalizedInductionFunctor.{uG, uV} hM hMM hL hU₀ ⋙
      normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁).obj A) ≅
    ((normalizedInductionFunctor.{uG, uV} h₀ hU₀).obj A) := by
  letI := hM.locallyCompactSpace
  let e := normalizedInductionStagesEquiv h₀ h₁ hM hMM hL hU₀ hU₁
    hUc₀ hUc₁ hLUc hδ hPP hUU hproj A
  refine SmoothRep.mkIso
    { toFun := fun f => e f
      invFun := fun f => e.symm f
      map_add' := fun f g => e.map_add f g
      map_smul' := fun c f => e.map_smul c f
      left_inv := fun f => e.symm_apply_apply f
      right_inv := fun f => e.apply_symm_apply f
      isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro f
  exact DFunLike.congr_fun (e.isIntertwining' g) f

/-- The stages map evaluates the inner induced function at the identity. -/
theorem normalizedInductionStagesAppIso_eval
    (A : SmoothRep.{0, uG, uV} ℂ M₀)
    (F : (leviNormalizedInductionFunctor.{uG, uV} hM hMM hL hU₀ ⋙
      normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁).obj A) (x : G) :
    Induction.eval P₀ (inducingRepresentation h₀ hU₀ A)
      (SmoothRep.hom (normalizedInductionStagesAppIso h₀ h₁ hM hMM hL hU₀ hU₁
        hUc₀ hUc₁ hLUc hδ hPP hUU hproj A).hom F) x =
      (F.1.1 x).1.1 1 := by
  change Induction.eval P₀ (inducingRepresentation h₀ hU₀ A)
    (normalizedInductionStagesEquiv h₀ h₁ hM hMM hL hU₀ hU₁
      hUc₀ hUc₁ hLUc hδ hPP hUU hproj A F) x = _
  simp only [normalizedInductionStagesEquiv, Representation.Equiv.trans_apply,
    Induction.smoothStagesEquiv_eval, Induction.smoothInducedEquiv_eval]
  change
    ((inductionCharacter U₁ M₁ hU₁ h₁.levi_le_normalizer).toMonoidHom
      (h₁.projection 1) : ℂ) • (F.1.1 x).1.1 (h₁.projection 1) =
      (F.1.1 x).1.1 1
  simp only [map_one, Units.val_one, one_smul]

/-- Normalized induction in stages, natural in the original fine-Levi
representation. -/
def normalizedInductionStagesIso :
    (leviNormalizedInductionFunctor.{uG, uV} hM hMM hL hU₀ ⋙
      normalizedInductionFunctor.{uG, max uG uV} h₁ hU₁) ≅
    normalizedInductionFunctor.{uG, uV} h₀ hU₀ := by
  refine NatIso.ofComponents
    (normalizedInductionStagesAppIso h₀ h₁ hM hMM hL hU₀ hU₁
      hUc₀ hUc₁ hLUc hδ hPP hUU hproj) ?_
  intro A B φ
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change Induction.eval P₀ (inducingRepresentation h₀ hU₀ B)
      (SmoothRep.hom (normalizedInductionStagesAppIso h₀ h₁ hM hMM hL hU₀ hU₁
        hUc₀ hUc₁ hLUc hδ hPP hUU hproj B).hom
        (SmoothRep.hom ((leviNormalizedInductionFunctor hM hMM hL hU₀ ⋙
          normalizedInductionFunctor h₁ hU₁).map φ) F)) x =
    Induction.eval P₀ (inducingRepresentation h₀ hU₀ B)
      (SmoothRep.hom ((normalizedInductionFunctor h₀ hU₀).map φ)
        (SmoothRep.hom (normalizedInductionStagesAppIso h₀ h₁ hM hMM hL hU₀ hU₁
          hUc₀ hUc₁ hLUc hδ hPP hUU hproj A).hom F)) x
  rw [normalizedInductionStagesAppIso_eval, normalizedInductionFunctor_map_eval,
    normalizedInductionStagesAppIso_eval]
  rfl

end Stages

end Langlands.Aubert.General
