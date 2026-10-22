import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.CMField

/-! # Arithmetic transport at finite places -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

universe u v w

private theorem intValuation_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S) (p : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap e.toRingHom e.surjective p).intValuation x =
      p.intValuation (e x) := by
  have hle (n : ℕ) :
      (HeightOneSpectrum.comap e.toRingHom e.surjective p).intValuation x ≤
        WithZero.exp (-(n : ℤ)) ↔
      p.intValuation (e x) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem]
    change x ∈ (p.asIdeal.comap e)^n ↔ e x ∈ p.asIdeal^n
    rw [← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm]
    rfl
  by_cases hx : x = 0
  · simp [hx]
  have he : e x ≠ 0 := by simpa using hx
  apply le_antisymm
  · rw [p.intValuation_if_neg he]
    apply (hle _).mpr
    rw [← p.intValuation_if_neg he]
  · rw [(HeightOneSpectrum.comap e.toRingHom e.surjective p).intValuation_if_neg hx]
    apply (hle _).mp
    rw [← (HeightOneSpectrum.comap e.toRingHom e.surjective p).intValuation_if_neg hx]

private theorem uniformContinuous_of_valuation_preserving
    {A : Type u} {B : Type v} {Γ : Type w}
    [Field A] [Field B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (e : A ≃+* B)
    (h : ∀ x, Valued.v (e x) = Valued.v x) : UniformContinuous e := by
  refine uniformContinuous_of_continuousAt_zero e.toAddMonoidHom ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero B Γ), true_and, forall_const]
  intro γ
  obtain ⟨b, hb⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation B Γ)) γ.val
  change Valued.v.restrict b = γ.val at hb
  have hb0 : b ≠ 0 := by
    intro hb0
    exact γ.ne_zero (by simpa [hb0] using hb.symm)
  have ha0 : Valued.v.restrict (e.symm b) ≠ 0 := by simpa using hb0
  refine ⟨Units.mk0 _ ha0, ?_⟩
  intro x hx
  change Valued.v.restrict (e x) < γ.val
  rw [← hb, Valuation.restrict_lt_iff]
  change Valued.v.restrict x < Valued.v.restrict (e.symm b) at hx
  rw [Valuation.restrict_lt_iff] at hx
  rw [h x, ← e.apply_symm_apply b, h (e.symm b)]
  exact hx

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [Field L] [Field M]

/-- Pullback of actual finite places along the induced ring-of-integers isomorphism. -/
def finitePlaceEquiv (e : K ≃+* L) :
    HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 K) :=
  (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm

@[simp] theorem finitePlaceEquiv_asIdeal (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv e p).asIdeal =
      p.asIdeal.comap (RingOfIntegers.mapRingEquiv e).toRingHom := rfl

@[simp] theorem finitePlaceEquiv_mem (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : 𝓞 K) :
    x ∈ (finitePlaceEquiv e p).asIdeal ↔
      RingOfIntegers.mapRingEquiv e x ∈ p.asIdeal := Iff.rfl

@[simp] theorem finitePlaceEquiv_refl :
    finitePlaceEquiv (RingEquiv.refl K) = Equiv.refl (HeightOneSpectrum (𝓞 K)) := by
  ext p x
  rfl

theorem finitePlaceEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    finitePlaceEquiv (e.trans f) = (finitePlaceEquiv f).trans (finitePlaceEquiv e) := by
  ext p x
  rfl

variable [NumberField K] [NumberField L] [NumberField M]

/-- Normalized adic valuations are preserved, not merely equivalent, under isomorphisms. -/
theorem finitePlaceEquiv_valuation (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L)) (x : K) :
    (finitePlaceEquiv e p).valuation K x = p.valuation L (e x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) x
  rw [map_div₀, map_div₀, map_div₀]
  have h (r : 𝓞 K) :
      (finitePlaceEquiv e p).valuation K (algebraMap (𝓞 K) K r) =
        p.valuation L (e (algebraMap (𝓞 K) K r)) := by
    change (finitePlaceEquiv e p).valuation K (algebraMap (𝓞 K) K r) =
      p.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv e r))
    rw [valuation_of_algebraMap, valuation_of_algebraMap]
    exact intValuation_comap (RingOfIntegers.mapRingEquiv e) p r
  rw [h a, h b]

private def finiteWithValEquiv (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L)) :
    WithVal ((finitePlaceEquiv e p).valuation K) ≃+* WithVal (p.valuation L) :=
  WithVal.congr _ _ e

private theorem uniformContinuous_finiteWithValEquiv (e : K ≃+* L)
    (p : HeightOneSpectrum (𝓞 L)) :
    UniformContinuous (finiteWithValEquiv e p) :=
  uniformContinuous_of_valuation_preserving _ fun x =>
    (finitePlaceEquiv_valuation e p x.ofVal).symm

private theorem uniformContinuous_finiteWithValEquiv_symm (e : K ≃+* L)
    (p : HeightOneSpectrum (𝓞 L)) :
    UniformContinuous (finiteWithValEquiv e p).symm :=
  uniformContinuous_of_valuation_preserving _ fun x => by
    change (finitePlaceEquiv e p).valuation K (e.symm x.ofVal) = p.valuation L x.ofVal
    rw [finitePlaceEquiv_valuation, e.apply_symm_apply]

/-- Transport of actual completed number fields at corresponding finite places. -/
def finiteCompletionEquiv (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv e p).adicCompletion K ≃+* p.adicCompletion L :=
  (adicCompletion.equiv K _).trans
    ((UniformSpace.Completion.mapRingEquiv (finiteWithValEquiv e p)
      (uniformContinuous_finiteWithValEquiv e p).continuous
      (uniformContinuous_finiteWithValEquiv_symm e p).continuous).trans
      (adicCompletion.equiv L p).symm)

theorem continuous_finiteCompletionEquiv (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L)) :
    Continuous (finiteCompletionEquiv e p) :=
  (adicCompletion.continuous_ofCompletion L p).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K _))

theorem continuous_finiteCompletionEquiv_symm (e : K ≃+* L)
    (p : HeightOneSpectrum (𝓞 L)) :
    Continuous (finiteCompletionEquiv e p).symm :=
  (adicCompletion.continuous_ofCompletion K _).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion L p))

def finiteCompletionHomeomorph (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv e p).adicCompletion K ≃ₜ p.adicCompletion L where
  __ := (finiteCompletionEquiv e p).toEquiv
  continuous_toFun := continuous_finiteCompletionEquiv e p
  continuous_invFun := continuous_finiteCompletionEquiv_symm e p

@[simp] theorem finiteCompletionEquiv_coe (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : K) :
    finiteCompletionEquiv e p (algebraMap K ((finitePlaceEquiv e p).adicCompletion K) x) =
      algebraMap L (p.adicCompletion L) (e x) := by
  apply (adicCompletion.equiv L p).injective
  change UniformSpace.Completion.mapRingHom (finiteWithValEquiv e p).toRingHom
    (uniformContinuous_finiteWithValEquiv e p).continuous
    (↑(WithVal.toVal ((finitePlaceEquiv e p).valuation K) x)) = _
  exact UniformSpace.Completion.mapRingHom_coe
    (f := (finiteWithValEquiv e p).toRingHom)
    (uniformContinuous_finiteWithValEquiv e p).continuous _

open scoped WithZeroTopology in
theorem finiteCompletionEquiv_valuation (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : (finitePlaceEquiv e p).adicCompletion K) :
    Valued.v (finiteCompletionEquiv e p x) = Valued.v x := by
  have h := (denseRange_algebraMap K (finitePlaceEquiv e p)).equalizer
    ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L p)).comp
      (continuous_finiteCompletionEquiv e p))
    (Valued.continuous_valuation_of_surjective
      (valuedAdicCompletion_surjective K (finitePlaceEquiv e p))) (by
        funext a
        change Valued.v (finiteCompletionEquiv e p
          (algebraMap K ((finitePlaceEquiv e p).adicCompletion K) a)) = _
        rw [finiteCompletionEquiv_coe]
        change Valued.v (↑(e a) : p.adicCompletion L) =
          Valued.v (↑a : (finitePlaceEquiv e p).adicCompletion K)
        rw [valuedAdicCompletion_eq_valuation', valuedAdicCompletion_eq_valuation']
        exact (finitePlaceEquiv_valuation e p a).symm)
  exact congrFun h x

theorem finiteCompletionEquiv_integral (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : (finitePlaceEquiv e p).adicCompletion K) :
    finiteCompletionEquiv e p x ∈ p.adicCompletionIntegers L ↔
      x ∈ (finitePlaceEquiv e p).adicCompletionIntegers K := by
  simp only [mem_adicCompletionIntegers, finiteCompletionEquiv_valuation]

@[simp] theorem finiteCompletionEquiv_refl (p : HeightOneSpectrum (𝓞 K))
    (x : p.adicCompletion K) :
    finiteCompletionEquiv (RingEquiv.refl K) p x = x := by
  have h := (denseRange_algebraMap K p).equalizer
    (continuous_finiteCompletionEquiv (RingEquiv.refl K) p) continuous_id (by
      funext a
      exact finiteCompletionEquiv_coe (RingEquiv.refl K) p a)
  exact congrFun h x

theorem finiteCompletionEquiv_trans (e : K ≃+* L) (f : L ≃+* M)
    (p : HeightOneSpectrum (𝓞 M)) (x : (finitePlaceEquiv (e.trans f) p).adicCompletion K) :
    finiteCompletionEquiv (e.trans f) p x =
      finiteCompletionEquiv f p (finiteCompletionEquiv e (finitePlaceEquiv f p) x) := by
  have h := (denseRange_algebraMap K (finitePlaceEquiv (e.trans f) p)).equalizer
    (continuous_finiteCompletionEquiv (e.trans f) p)
    ((continuous_finiteCompletionEquiv f p).comp
      (continuous_finiteCompletionEquiv e (finitePlaceEquiv f p))) (by
        funext a
        change finiteCompletionEquiv (e.trans f) p
          (algebraMap K ((finitePlaceEquiv (e.trans f) p).adicCompletion K) a) =
          finiteCompletionEquiv f p (finiteCompletionEquiv e (finitePlaceEquiv f p)
            (algebraMap K ((finitePlaceEquiv (e.trans f) p).adicCompletion K) a))
        calc
          _ = algebraMap M (p.adicCompletion M) (f (e a)) :=
            finiteCompletionEquiv_coe (e.trans f) p a
          _ = finiteCompletionEquiv f p
              (algebraMap L ((finitePlaceEquiv f p).adicCompletion L) (e a)) :=
            (finiteCompletionEquiv_coe f p (e a)).symm
          _ = _ := congrArg (finiteCompletionEquiv f p)
            (finiteCompletionEquiv_coe e (finitePlaceEquiv f p) a).symm)
  exact congrFun h x

private theorem finiteCompletion_mapsTo (e : K ≃+* L) :
    ∀ᶠ p in Filter.cofinite,
      Set.MapsTo (finiteCompletionEquiv e p)
        ((finitePlaceEquiv e p).adicCompletionIntegers K) (p.adicCompletionIntegers L) :=
  Filter.Eventually.of_forall fun p x hx => (finiteCompletionEquiv_integral e p x).mpr hx

/-- The actual restricted-product map; integrality holds at every transported place. -/
def finiteAdeleMap (e : K ≃+* L) : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom _ _ (finitePlaceEquiv e)
    (finitePlaceEquiv e).injective.tendsto_cofinite
    (fun p => (finiteCompletionEquiv e p).toRingHom) (finiteCompletion_mapsTo e)

@[simp] theorem finiteAdeleMap_apply (e : K ≃+* L) (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleMap e x p = finiteCompletionEquiv e p (x (finitePlaceEquiv e p)) := rfl

theorem continuous_finiteAdeleMap (e : K ≃+* L) : Continuous (finiteAdeleMap e) :=
  RestrictedProduct.mapAlong_continuous _ _ (finitePlaceEquiv e)
    (finitePlaceEquiv e).injective.tendsto_cofinite
    (fun p => finiteCompletionEquiv e p) (finiteCompletion_mapsTo e)
    (continuous_finiteCompletionEquiv e)

@[simp] theorem finiteAdeleMap_diagonal (e : K ≃+* L) (x : K) :
    finiteAdeleMap e (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap L (FiniteAdeleRing (𝓞 L) L) (e x) := by
  apply FiniteAdeleRing.ext
  intro p
  exact finiteCompletionEquiv_coe e p x

@[simp] theorem finiteAdeleMap_refl :
    finiteAdeleMap (RingEquiv.refl K) = RingHom.id (FiniteAdeleRing (𝓞 K) K) := by
  apply RingHom.ext
  intro x
  apply FiniteAdeleRing.ext
  intro p
  exact finiteCompletionEquiv_refl p (x p)

theorem finiteAdeleMap_trans (e : K ≃+* L) (f : L ≃+* M) :
    finiteAdeleMap (e.trans f) = (finiteAdeleMap f).comp (finiteAdeleMap e) := by
  apply RingHom.ext
  intro x
  apply FiniteAdeleRing.ext
  intro p
  exact finiteCompletionEquiv_trans e f p (x (finitePlaceEquiv (e.trans f) p))

/-- Ring isomorphism of the genuine finite adele restricted products. -/
def finiteAdeleEquiv (e : K ≃+* L) : FiniteAdeleRing (𝓞 K) K ≃+* FiniteAdeleRing (𝓞 L) L where
  __ := finiteAdeleMap e
  invFun := finiteAdeleMap e.symm
  left_inv x := by
    have h := finiteAdeleMap_trans e e.symm
    rw [RingEquiv.self_trans_symm, finiteAdeleMap_refl] at h
    exact (RingHom.congr_fun h x).symm
  right_inv x := by
    have h := finiteAdeleMap_trans e.symm e
    rw [RingEquiv.symm_trans_self, finiteAdeleMap_refl] at h
    exact (RingHom.congr_fun h x).symm

theorem continuous_finiteAdeleEquiv (e : K ≃+* L) : Continuous (finiteAdeleEquiv e) :=
  continuous_finiteAdeleMap e

theorem continuous_finiteAdeleEquiv_symm (e : K ≃+* L) :
    Continuous (finiteAdeleEquiv e).symm := continuous_finiteAdeleMap e.symm

def finiteAdeleHomeomorph (e : K ≃+* L) :
    FiniteAdeleRing (𝓞 K) K ≃ₜ FiniteAdeleRing (𝓞 L) L where
  __ := (finiteAdeleEquiv e).toEquiv
  continuous_toFun := continuous_finiteAdeleEquiv e
  continuous_invFun := continuous_finiteAdeleEquiv_symm e

@[simp] theorem finiteAdeleEquiv_apply (e : K ≃+* L) (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleEquiv e x p = finiteCompletionEquiv e p (x (finitePlaceEquiv e p)) := rfl

@[simp] theorem finiteAdeleEquiv_diagonal (e : K ≃+* L) (x : K) :
    finiteAdeleEquiv e (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap L (FiniteAdeleRing (𝓞 L) L) (e x) := finiteAdeleMap_diagonal e x

@[simp] theorem finiteAdeleEquiv_refl :
    finiteAdeleEquiv (RingEquiv.refl K) = RingEquiv.refl (FiniteAdeleRing (𝓞 K) K) := by
  apply RingEquiv.ext
  intro x
  exact RingHom.congr_fun finiteAdeleMap_refl x

theorem finiteAdeleEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    finiteAdeleEquiv (e.trans f) = (finiteAdeleEquiv e).trans (finiteAdeleEquiv f) := by
  apply RingEquiv.ext
  intro x
  exact RingHom.congr_fun (finiteAdeleMap_trans e f) x

end Langlands.Global.AdelicFunctoriality
