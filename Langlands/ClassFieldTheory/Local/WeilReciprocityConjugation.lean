import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport
import Langlands.LocalFactor.RankOne
import Langlands.LocalClassField.AbelianizationTransport

/-! # Local reciprocity under compatible conjugation -/

noncomputable section

namespace Langlands.LocalClassField.WeilReciprocityTransport

universe u v

open Weil.Local WeilReciprocityUniqueness ReciprocitySystemUniqueness

section Uniqueness

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

theorem candidateGaloisHom_eq_of_order_ne_zero
    {e₁ e₂ : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)}
    (h₁ : LocalReciprocityCandidateRelation T (Weil.Local.localResidueDegree F) e₁)
    (h₂ : LocalReciprocityCandidateRelation T (Weil.Local.localResidueDegree F) e₂)
    (a : F.Carrierˣ) (ha : T.ord (a : F.Carrier) ≠ 0) :
    candidateGaloisHom T (Weil.Local.localResidueDegree F) e₁ a =
      candidateGaloisHom T (Weil.Local.localResidueDegree F) e₂ a := by
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let := absoluteGaloisNonarchimedean F.Carrier
  let := abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  let := quotientNonarchimedean
    (commutator (Field.absoluteGaloisGroup F.Carrier)).topologicalClosure
  refine eq_of_forall_openSubgroup ?_ (T.ord (a : F.Carrier)) ha ?_
  · intro H hH hmem
    exact (mem_openSubgroup_iff h₁.2 h₂.2 H hH a).mp hmem
  · intro N hN
    let : NeZero N := ⟨hN⟩
    refine ⟨(degreeMod F N).toMonoidHom, ?_, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod N)))).preimage
        (degreeMod F N).continuous
    · change degreeMod F N
        (WeilQuotients.toGroupAbelianization (Weil.Local.localResidueDegree F)
          (e₁.symm a)) = _
      rw [degreeMod_toGroupAbelianization]
      have h := DFunLike.congr_fun h₁.1 (e₁.symm a)
      change T.orderHom (e₁ (e₁.symm a)) =
        WeilQuotients.degree _ (e₁.symm a) at h
      rw [e₁.apply_symm_apply] at h
      have hd : WeilQuotients.degree (Weil.Local.localResidueDegree F) (e₁.symm a) =
          T.orderHom a := h.symm
      rw [hd]
      rfl
    · change degreeMod F N
        (WeilQuotients.toGroupAbelianization (Weil.Local.localResidueDegree F)
          (e₂.symm a)) = _
      rw [degreeMod_toGroupAbelianization]
      have h := DFunLike.congr_fun h₂.1 (e₂.symm a)
      change T.orderHom (e₂ (e₂.symm a)) =
        WeilQuotients.degree _ (e₂.symm a) at h
      rw [e₂.apply_symm_apply] at h
      have hd : WeilQuotients.degree (Weil.Local.localResidueDegree F) (e₂.symm a) =
          T.orderHom a := h.symm
      rw [hd]
      rfl

/-- Uniformizer cancellation extends comparison to all field units. -/
theorem candidateGaloisHom_eq
    {e₁ e₂ : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)}
    (h₁ : LocalReciprocityCandidateRelation T (Weil.Local.localResidueDegree F) e₁)
    (h₂ : LocalReciprocityCandidateRelation T (Weil.Local.localResidueDegree F) e₂)
    (a : F.Carrierˣ) :
    candidateGaloisHom T (Weil.Local.localResidueDegree F) e₁ a =
      candidateGaloisHom T (Weil.Local.localResidueDegree F) e₂ a := by
  let := T.topology
  by_cases ha : T.ord (a : F.Carrier) ≠ 0
  · exact candidateGaloisHom_eq_of_order_ne_zero F T h₁ h₂ a ha
  · have ha0 : T.ord (a : F.Carrier) = 0 := not_ne_iff.mp ha
    let π := LocalFactor.PadicAbelian.uniformizerUnit T
    have hπ : T.ord (π : F.Carrier) = 1 :=
      LocalFactor.PadicAbelian.uniformizerUnit_ord T
    have hap : T.ord ((a * π : F.Carrierˣ) : F.Carrier) ≠ 0 := by
      change T.ord ((a : F.Carrier) * (π : F.Carrier)) ≠ 0
      rw [T.ord_mul a.ne_zero π.ne_zero, ha0, hπ]
      norm_num
    have heπ := candidateGaloisHom_eq_of_order_ne_zero F T h₁ h₂ π (by
      rw [hπ]
      norm_num)
    have heap := candidateGaloisHom_eq_of_order_ne_zero F T h₁ h₂ (a * π) hap
    rw [map_mul, map_mul, heπ] at heap
    exact mul_right_cancel heap


/-- Order normalization and finite norm-residue kernels already imply uniqueness. -/
theorem candidate_eq
    {e₁ e₂ : WeilReciprocityCandidate T (localResidueDegree F)}
    (h₁ : LocalReciprocityCandidateRelation T (localResidueDegree F) e₁)
    (h₂ : LocalReciprocityCandidateRelation T (localResidueDegree F) e₂) : e₁ = e₂ := by
  let := T.topology
  have hinv : ∀ a : F.Carrierˣ, e₁.symm a = e₂.symm a := by
    intro a
    apply WeilReciprocityUniqueness.toGroupAbelianization_injective F
    exact candidateGaloisHom_eq F T h₁ h₂ a
  apply ContinuousMulEquiv.ext
  intro w
  have hw := hinv (e₁ w)
  rw [ContinuousMulEquiv.symm_apply_apply] at hw
  exact (congrArg e₂ hw).trans (e₂.apply_symm_apply (e₁ w)) |>.symm

end Uniqueness

section Restriction

variable {K : Type u} [Field K]

/-- Finite restriction acts on the same elements of the chosen algebraic closure. -/
theorem restriction_apply_coe (L : FiniteAbelianExtension K)
    (σ : Field.absoluteGaloisGroup K) (x : L.field) :
    (L.restriction σ x : AlgebraicClosure K) = AlgEquiv.toAlgHom σ x := by
  exact congrArg (fun y : AlgebraicClosure K => y)
    (AlgEquiv.restrictNormal_commutes σ L.field x)

end Restriction

section Conjugation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (b : F.Carrier ≃+* F.Carrier)
  (θ : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure F.Carrier)
  (hθ : (algebraMap F.Carrier (AlgebraicClosure F.Carrier)).comp b.toRingHom =
    θ.toRingHom.comp (algebraMap F.Carrier (AlgebraicClosure F.Carrier)))
  (c : localWeilGroup F ≃ₜ* localWeilGroup F)
  (hc : ∀ (y : localWeilGroup F) (x : AlgebraicClosure F.Carrier),
    AlgEquiv.toAlgHom (localProjection F (c y)) (θ x) =
      θ (AlgEquiv.toAlgHom (localProjection F y) x))

include hc in
/-- Finite restrictions transform by the induced field conjugation. -/
theorem restriction_conjugation (L : FiniteAbelianExtension F.Carrier)
    (y : localWeilGroup F) :
    (FiniteArtinTransport.extension b θ hθ L).restriction (localProjection F (c y)) =
      FiniteArtinTransport.extensionGaloisEquiv b θ hθ L
        (L.restriction (localProjection F y)) := by
  ext x
  change (((FiniteArtinTransport.extension b θ hθ L).restriction
      (localProjection F (c y))) x : AlgebraicClosure F.Carrier) =
    (FiniteArtinTransport.extensionGaloisEquiv b θ hθ L
      (L.restriction (localProjection F y)) x : AlgebraicClosure F.Carrier)
  rw [restriction_apply_coe, FiniteArtinTransport.extensionGaloisEquiv_apply_coe,
    restriction_apply_coe]
  simpa only [RingEquiv.apply_symm_apply] using hc y (θ.symm x)


variable (T : F.TopologicalData)

/-- The continuous units equivalence induced by the base field automorphism. -/
def unitsEquiv (hb : letI := T.topology; Continuous b)
    (hb' : letI := T.topology; Continuous b.symm) :
    letI := T.topology; F.Carrierˣ ≃ₜ* F.Carrierˣ := by
  letI := T.topology
  exact { Units.mapEquiv b.toMulEquiv with
    continuous_toFun := hb.units_map _
    continuous_invFun := hb'.units_map _ }

/-- Conjugate a supplied reciprocity candidate through the two actual equivalences. -/
def transportedCandidate (hb : letI := T.topology; Continuous b)
    (hb' : letI := T.topology; Continuous b.symm)
    (e : WeilReciprocityCandidate T (localResidueDegree F)) :
    WeilReciprocityCandidate T (localResidueDegree F) := by
  letI := T.topology
  exact ((abelianizationCongr c).trans e).trans (unitsEquiv F b T hb hb').symm

include hc in
/-- The finite family of a transported candidate is the published finite Artin pullback. -/
theorem transportedCandidate_finiteFamily (hb : letI := T.topology; Continuous b)
    (hb' : letI := T.topology; Continuous b.symm)
    (e : WeilReciprocityCandidate T (localResidueDegree F)) :
    letI := T.topology
    finiteFamilyOfHom (candidateGaloisHom T (localResidueDegree F)
        (transportedCandidate F b c T hb hb' e)) =
      FiniteArtinTransport.pullback b θ hθ hb
        (finiteFamilyOfHom (candidateGaloisHom T (localResidueDegree F) e)) := by
  letI := T.topology
  funext L
  apply ContinuousMonoidHom.ext
  intro a
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    ((commutator (localWeilGroup F)).topologicalClosure)
      (e.symm (unitsEquiv F b T hb hb' a))
  change QuotientGroup.mk y = e.symm (unitsEquiv F b T hb hb' a) at hy
  change L.abelianRestriction
      (WeilQuotients.toGroupAbelianization (localResidueDegree F)
        ((abelianizationCongr c).symm (e.symm (unitsEquiv F b T hb hb' a)))) =
    (FiniteArtinTransport.extensionGaloisEquiv b θ hθ L).symm
      ((FiniteArtinTransport.extension b θ hθ L).abelianRestriction
        (WeilQuotients.toGroupAbelianization (localResidueDegree F)
          (e.symm (unitsEquiv F b T hb hb' a))))
  rw [← hy]
  change L.restriction (localProjection F (c.symm y)) =
    (FiniteArtinTransport.extensionGaloisEquiv b θ hθ L).symm
      ((FiniteArtinTransport.extension b θ hθ L).restriction (localProjection F y))
  apply (FiniteArtinTransport.extensionGaloisEquiv b θ hθ L).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  have h := restriction_conjugation F b θ hθ c hc L (c.symm y)
  rw [c.apply_symm_apply] at h
  exact h.symm

include hc hθ in
/-- Order and finite norm-residue conditions are preserved by compatible conjugation. -/
theorem transportedCandidate_relation (hb : letI := T.topology; Continuous b)
    (hb' : letI := T.topology; Continuous b.symm)
    (hb_order : ∀ a : F.Carrierˣ,
      T.orderHom (Units.mapEquiv b.toMulEquiv a) = T.orderHom a)
    (hc_degree : ∀ y : localWeilGroup F, localDegree F (c y) = localDegree F y)
    (e : WeilReciprocityCandidate T (localResidueDegree F))
    (he : LocalReciprocityCandidateRelation T (localResidueDegree F) e) :
    LocalReciprocityCandidateRelation T (localResidueDegree F)
      (transportedCandidate F b c T hb hb' e) := by
  letI := T.topology
  constructor
  · apply MonoidHom.ext
    intro w
    change T.orderHom ((unitsEquiv F b T hb hb').symm
      (e (abelianizationCongr c w))) = WeilQuotients.degree (localResidueDegree F) w
    have horder : ∀ z : F.Carrierˣ,
        T.orderHom ((unitsEquiv F b T hb hb').symm z) = T.orderHom z := by
      intro z
      have h := hb_order ((unitsEquiv F b T hb hb').symm z)
      change T.orderHom (unitsEquiv F b T hb hb'
        ((unitsEquiv F b T hb hb').symm z)) = _ at h
      rw [ContinuousMulEquiv.apply_symm_apply] at h
      exact h.symm
    rw [horder]
    have heq := DFunLike.congr_fun he.1 (abelianizationCongr c w)
    change T.orderHom (e (abelianizationCongr c w)) =
      WeilQuotients.degree (localResidueDegree F) (abelianizationCongr c w) at heq
    rw [heq]
    induction w using QuotientGroup.induction_on with
    | H y => exact hc_degree y
  · constructor
    · apply he.2.1.mono
      rintro _ ⟨a, rfl⟩
      refine ⟨transportedCandidate F b c T hb hb' e (e.symm a), ?_⟩
      change WeilQuotients.toGroupAbelianization (localResidueDegree F)
          ((transportedCandidate F b c T hb hb' e).symm
            (transportedCandidate F b c T hb hb' e (e.symm a))) = _
      rw [ContinuousMulEquiv.symm_apply_apply]
      rfl
    · rw [transportedCandidate_finiteFamily F b θ hθ c hc T hb hb' e]
      exact FiniteArtinTransport.pullback_finiteArtinSystemRelation b θ hθ hb _ he.2.2

include hc hθ in
/-- Local reciprocity is equivariant under compatible degree-preserving conjugation. -/
theorem reciprocity_conjugation (hb : letI := T.topology; Continuous b)
    (hb' : letI := T.topology; Continuous b.symm)
    (hb_order : ∀ a : F.Carrierˣ,
      T.orderHom (Units.mapEquiv b.toMulEquiv a) = T.orderHom a)
    (hc_degree : ∀ y : localWeilGroup F, localDegree F (c y) = localDegree F y)
    (e : WeilReciprocityCandidate T (localResidueDegree F))
    (he : LocalReciprocityCandidateRelation T (localResidueDegree F) e)
    (y : localWeilGroup F) :
    letI := T.topology
    e (WeilQuotients.projection (localResidueDegree F) (c y)) =
      Units.mapEquiv b.toMulEquiv
        (e (WeilQuotients.projection (localResidueDegree F) y)) := by
  letI := T.topology
  have heq := candidate_eq F T
    (transportedCandidate_relation F b θ hθ c hc T hb hb' hb_order hc_degree e he) he
  have hy := DFunLike.congr_fun heq (WeilQuotients.projection (localResidueDegree F) y)
  change (unitsEquiv F b T hb hb').symm
    (e (WeilQuotients.projection (localResidueDegree F) (c y))) =
      e (WeilQuotients.projection (localResidueDegree F) y) at hy
  apply (unitsEquiv F b T hb hb').symm.injective
  rw [hy]
  exact ((unitsEquiv F b T hb hb').symm_apply_apply _).symm

end Conjugation

end Langlands.LocalClassField.WeilReciprocityTransport
