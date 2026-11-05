import Langlands.Representation.Plancherel.CompactInductionGeneration
import Langlands.Representation.Plancherel.CompactIntertwiningWeakRegularity
import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement

/-! # Transport of compact integral domination to twist-orbit saturations -/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe uG uI uV

section Saturation

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) (U' : Subgroup G)

/-- The compact section obtained by applying a linear automorphism of the
carrier that commutes with the action of `M` up to two unramified characters. -/
def compactSectionEquivMap (ψ₀ χ₀ : unramifiedCharacters ν) (e : A ≃ₗ[ℂ] A)
    (he : ∀ (m : M) (v : A), e ((ψ₀.val m : ℂ) • A.representation m v) =
      (χ₀.val m : ℂ) • A.representation m (e v))
    (f : CompactInductionPicture h K A) : CompactInductionPicture h K A :=
  smoothFunctionOf (P.comap K.toSubgroup.subtype) (compactPictureInducingRepresentation h K A)
    (fun x => e.symm (f.1.1 x))
    (by
      intro p x
      have hcov : f.1.1 ((p : K) * x) = compactPictureInducingRepresentation h K A p (f.1.1 x) :=
        f.1.2 p x
      change e.symm (f.1.1 ((p : K) * x)) =
        compactPictureInducingRepresentation h K A p (e.symm (f.1.1 x))
      rw [hcov]
      have hp' : K.toSubgroup.subtype.subgroupComap P p ∈ conjOpenSubgroup P K 1 := by
        apply mem_conjOpenSubgroup.mpr
        simp only [inv_one, one_mul, mul_one]
        exact (p.1 : K).2
      have h1 := unramifiedPullback_eq_one_of_mem_conjOpenSubgroup P hP ν hν h.projection hr
        ψ₀ K hK 1 hp'
      have h2 := unramifiedPullback_eq_one_of_mem_conjOpenSubgroup P hP ν hν h.projection hr
        χ₀ K hK 1 hp'
      have key := he (h.projection (K.toSubgroup.subtype.subgroupComap P p)) (e.symm (f.1.1 x))
      rw [h1, h2, Units.val_one, one_smul, one_smul, e.apply_symm_apply] at key
      change e.symm (A.representation (h.projection (K.toSubgroup.subtype.subgroupComap P p))
        (f.1.1 x)) = A.representation (h.projection (K.toSubgroup.subtype.subgroupComap P p))
          (e.symm (f.1.1 x))
      rw [← key, e.symm_apply_apply])
    (Classical.choose f.property)
    (by
      intro l x
      have hl := congrArg (fun F => F.1 x) (Classical.choose_spec f.property l)
      change e.symm (f.1.1 (x * l)) = e.symm (f.1.1 x)
      congr 1)

omit [LocallyCompactSpace G] in
theorem eval_compactSectionEquivMap (ψ₀ χ₀ : unramifiedCharacters ν) (e : A ≃ₗ[ℂ] A)
    (he : ∀ (m : M) (v : A), e ((ψ₀.val m : ℂ) • A.representation m v) =
      (χ₀.val m : ℂ) • A.representation m (e v))
    (f : CompactInductionPicture h K A) (x : K) :
    eval _ _ (compactSectionEquivMap h K hP hK ν hν hr A ψ₀ χ₀ e he f) x =
      e.symm (eval _ _ f x) := rfl

/-- The actual quotient integrand at `χ` of a compact section is `e` applied to
the integrand of the transported section at `χ χ₀⁻¹ ψ₀`. -/
theorem unramifiedCompactIntegrand_compactSectionEquivMap (ψ₀ χ₀ : unramifiedCharacters ν)
    (e : A ≃ₗ[ℂ] A)
    (he : ∀ (m : M) (v : A), e ((ψ₀.val m : ℂ) • A.representation m v) =
      (χ₀.val m : ℂ) • A.representation m (e v))
    (f : CompactInductionPicture h K A) (χ : unramifiedCharacters ν) (g : G)
    (q : QuotientSpace (U := U) U') :
    unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g χ q =
      e (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U'
        (compactSectionEquivMap h K hP hK ν hν hr A ψ₀ χ₀ e he f) g (χ * χ₀⁻¹ * ψ₀) q) := by
  induction q using Quotient.inductionOn with
  | h u' =>
    change eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)
        ((u' : G) * g) =
      e (eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr
        (χ * χ₀⁻¹ * ψ₀) A).symm (compactSectionEquivMap h K hP hK ν hν hr A ψ₀ χ₀ e he f))
        ((u' : G) * g))
    obtain ⟨p, k, hpk⟩ := hPK ((u' : G) * g)
    rw [hpk]
    have e1 := extension_eval_mul h hU hδ K hP hK hPK ν hν hr A χ f p k
    have e2 := extension_eval_mul h hU hδ K hP hK hPK ν hν hr A (χ * χ₀⁻¹ * ψ₀)
      (compactSectionEquivMap h K hP hK ν hν hr A ψ₀ χ₀ e he f) p k
    rw [eval_compactSectionEquivMap] at e2
    set m := h.projection p
    set v := eval _ _ f k
    have key := he m (e.symm v)
    rw [e.apply_symm_apply] at key
    have hs : inductionScalar h hU ν (χ * χ₀⁻¹ * ψ₀) p =
        (inductionScalar h hU ν χ p * ((χ₀.val m)⁻¹ : ℂˣ)) * (ψ₀.val m : ℂ) := by
      simp only [inductionScalar, m]
      simp [mul_assoc]
      exact Units.val_inv_eq_inv_val _
    have mid : inductionScalar h hU ν χ p • A.representation m v =
        e (inductionScalar h hU ν (χ * χ₀⁻¹ * ψ₀) p • A.representation m (e.symm v)) := by
      rw [hs, mul_smul, map_smul, key, smul_smul, mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, mul_one]
    exact e1.trans (mid.trans (congrArg e e2.symm))

omit [LocallyCompactSpace G] in
/-- A smooth functional composed with a linear automorphism of the carrier that
commutes with the action of `M` up to two unramified characters. -/
def smoothDualEquivComp (ψ₀ χ₀ : unramifiedCharacters ν) (e : A ≃ₗ[ℂ] A)
    (he : ∀ (m : M) (v : A), e ((ψ₀.val m : ℂ) • A.representation m v) =
      (χ₀.val m : ℂ) • A.representation m (e v))
    (ℓ : Langlands.SmoothDual A.representation) : Langlands.SmoothDual A.representation :=
  ⟨ℓ.val ∘ₗ e.toLinearMap, by
    obtain ⟨L, hL⟩ := ℓ.property
    let Lψ : OpenSubgroup M :=
      { toSubgroup := ψ₀.val.toMonoidHom.ker, isOpen' := unramifiedCharacter_isOpen_ker ν ψ₀ }
    let Lχ : OpenSubgroup M :=
      { toSubgroup := χ₀.val.toMonoidHom.ker, isOpen' := unramifiedCharacter_isOpen_ker ν χ₀ }
    refine ⟨L ⊓ Lψ ⊓ Lχ, fun m => ?_⟩
    obtain ⟨⟨hmL, hmψ⟩, hmχ⟩ := m.property
    have h1 : ψ₀.val ((m : M)⁻¹) = 1 := by
      rw [map_inv]
      have : ψ₀.val (m : M) = 1 := hmψ
      rw [this, inv_one]
    have h2 : χ₀.val ((m : M)⁻¹) = 1 := by
      rw [map_inv]
      have : χ₀.val (m : M) = 1 := hmχ
      rw [this, inv_one]
    apply LinearMap.ext
    intro v
    change ℓ.val (e (A.representation (m : M)⁻¹ v)) = ℓ.val (e v)
    have key := he (m : M)⁻¹ v
    rw [h1, h2, Units.val_one, one_smul, one_smul] at key
    rw [key]
    have hfix := congrArg (fun φ : Module.Dual ℂ A => φ (e v)) (hL ⟨(m : M), hmL⟩)
    exact hfix⟩

omit [LocallyCompactSpace G] in
theorem smoothDualEquivComp_apply (ψ₀ χ₀ : unramifiedCharacters ν) (e : A ≃ₗ[ℂ] A)
    (he : ∀ (m : M) (v : A), e ((ψ₀.val m : ℂ) • A.representation m v) =
      (χ₀.val m : ℂ) • A.representation m (e v))
    (ℓ : Langlands.SmoothDual A.representation) (v : A) :
    (smoothDualEquivComp ν A ψ₀ χ₀ e he ℓ).val v = ℓ.val (e v) := rfl

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

/-- Local integrable domination on an open set of unramified parameters
extends to its actual twist-orbit saturation. -/
theorem compactIntegralLocallyDominatedOn_saturation {C : Set (unramifiedCharacters ν)}
    (hC : IsOpen C)
    (hdom : CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr A U' qν C) :
    CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr A U' qν
      (unramifiedTwistOrbitSaturation ν A C) := by
  intro f k ℓ χ₀
  obtain ⟨ψ₀, hψ₀, ⟨iso⟩⟩ := (mem_unramifiedTwistOrbitSaturation_iff ν A C χ₀.val).mp χ₀.property
  let E := SmoothRep.equivOfIso iso
  let e : A ≃ₗ[ℂ] A := E.toLinearEquiv
  have he : ∀ (m : M) (v : A), e ((ψ₀.val m : ℂ) • A.representation m v) =
      (χ₀.val.val m : ℂ) • A.representation m (e v) :=
    fun m v => E.toIntertwiningMap.isIntertwining _ _ m v
  let f' := compactSectionEquivMap h K hP hK ν hν hr A ψ₀ χ₀.val e he f
  let ℓ' := smoothDualEquivComp ν A ψ₀ χ₀.val e he ℓ
  obtain ⟨bound, hbint, hev⟩ := hdom f' k ℓ' ⟨ψ₀, hψ₀⟩
  refine ⟨bound, hbint, ?_⟩
  have hev' : ∀ᶠ ψ in 𝓝 ψ₀, ∀ᵐ q ∂qν,
      ‖ℓ'.val (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f' k ψ q)‖ ≤
        bound q := by
    rw [nhds_subtype, Filter.eventually_comap] at hev
    filter_upwards [hev, hC.mem_nhds hψ₀] with ψ hψ hψC
    exact hψ ⟨ψ, hψC⟩ rfl
  let Φ : unramifiedTwistOrbitSaturation ν A C → unramifiedCharacters ν :=
    fun χ => χ.val * χ₀.val⁻¹ * ψ₀
  have hΦ : Continuous Φ :=
    (continuous_subtype_val.mul continuous_const).mul continuous_const
  have hΦ₀ : Φ χ₀ = ψ₀ := by simp [Φ]
  have ht : Tendsto Φ (𝓝 χ₀) (𝓝 ψ₀) := hΦ₀ ▸ hΦ.tendsto χ₀
  filter_upwards [ht.eventually hev'] with χ hχ
  filter_upwards [hχ] with q hq
  rw [unramifiedCompactIntegrand_compactSectionEquivMap h hU hδ K hP hK hPK ν hν hr A U' ψ₀
    χ₀.val e he f χ.val (k : G) q]
  exact hq

end Saturation

end Langlands.Plancherel
