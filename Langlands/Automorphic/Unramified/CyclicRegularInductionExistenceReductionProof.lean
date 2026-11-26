import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof
import Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceReductionStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityReduction
import Langlands.Automorphic.Unramified.IsobaricSpectralUniqueness
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.AdelicFunctoriality.FinitePlaceEquivUnder
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterProof

/-!
# Building cyclic regular induction from prime orbit realizations

Proves `CyclicRegularInductionExistenceReductionStatement`: the prime orbit realization,
the constituent-pair comparison, the reverse orbit comparison, weak base-change
equivariance, Euler constituent recovery, transitivity of weak induction and the existence
of spectral attachments give an actual unitary cuspidal weak induction of every regular
unitary cusp over a cyclic extension of any degree (Arthur and Clozel 1989, Lemma III.6.4).

The common argument
`CyclicRegularInductionExistence.cyclicRegularInductionExistenceOver_of_inputs` is a strong
induction on `[E : F]` with the lower field fixed. Degree one transports the cusp
along the field isomorphism; prime degree uses the pair count to obtain the norm-character
self-twist of the prime realization and then the reverse comparison; composite degree takes
the fixed field `K` of a subgroup of prime order, shows that the cusp obtained over `K`
is regular for `K/F` by equivariance and recovery, and composes the two weak inductions.
The totally complex reduction applies the same argument in
`CyclicRegularInductionExistenceReductionTCProof`.
-/

noncomputable section

open scoped BigOperators NumberField

universe uF uE uV uW uA uB uP uQ

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace CyclicRegularInductionExistence

/-! ### Regularity under a cyclic Galois group -/

section Regular

variable {A : Type uA} {B : Type uB} [Field A] [Field B] [NumberField B] [Algebra A B]
  [CompactSpace (AdeleQuotient B)]

/-- If no nonidentity power of a generator below its order fixes a class, then only the
identity fixes it. -/
theorem eq_one_of_isGaloisStable [FiniteDimensional A B] (σ : B ≃ₐ[A] B)
    (hgen : ∀ τ : B ≃ₐ[A] B, τ ∈ Subgroup.zpowers σ) {m : ℕ} (c : IsoClass B m)
    (hreg : ∀ i : ℕ, 0 < i → i < orderOf σ → ¬ c.IsGaloisStable (σ ^ i))
    (τ : B ≃ₐ[A] B) (hτ : c.IsGaloisStable τ) : τ = 1 := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp (hgen τ))
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd hτ (hreg i hpos (Finset.mem_range.mp hi))

/-- Conversely, a class fixed only by the identity is fixed by no power of a generator
strictly between `0` and its order. -/
theorem not_isGaloisStable_pow (σ : B ≃ₐ[A] B) {m : ℕ} (c : IsoClass B m)
    (htriv : ∀ τ : B ≃ₐ[A] B, c.IsGaloisStable τ → τ = 1) (i : ℕ) (hi0 : 0 < i)
    (hi : i < orderOf σ) : ¬ c.IsGaloisStable (σ ^ i) :=
  fun h => pow_ne_one_of_lt_orderOf hi0.ne' hi (htriv _ h)

/-- The Galois orbit of a class fixed only by the identity has distinct constituents. -/
theorem galoisOrbit_nodup [FiniteDimensional A B] {m : ℕ} (c : IsoClass B m)
    (htriv : ∀ τ : B ≃ₐ[A] B, c.IsGaloisStable τ → τ = 1) :
    (IsobaricData.galoisOrbit A (PositiveRankCuspidalClass.ofFixedRank c)).Nodup := by
  classical
  let d := PositiveRankCuspidalClass.ofFixedRank c
  have hinj : Function.Injective (fun τ : B ≃ₐ[A] B => d.galoisConj τ) := by
    intro a b hab
    change d.galoisConj a = d.galoisConj b at hab
    have hfix : d.galoisConj (b⁻¹ * a) = d := by
      rw [PositiveRankCuspidalClass.galoisConj_mul, hab,
        ← PositiveRankCuspidalClass.galoisConj_mul, inv_mul_cancel,
        PositiveRankCuspidalClass.galoisConj_one]
    have hone : b⁻¹ * a = 1 := htriv _
      ((PositiveRankCuspidalClass.isGaloisStable_iff_galoisConj_ofFixedRank _ c).mpr hfix)
    exact (inv_mul_eq_one.mp hone).symm
  exact Multiset.Nodup.map hinj (Finset.univ : Finset (B ≃ₐ[A] B)).nodup

/-- The Galois orbit of a cusp with unitary central character is unitary. -/
theorem isUnitary_galoisOrbit [FiniteDimensional A B] {m : ℕ}
    (T : CuspidalOperatorRealization B m) (hT : HasUnitaryCentralCharacter T) :
    (IsobaricData.galoisOrbit A (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).IsUnitary := by
  intro c hc
  obtain ⟨τ, _, rfl⟩ := Multiset.mem_map.mp hc
  let e := τ.toRingEquiv.symm
  change (T.arithmeticComap e).realization.IsUnitarizable
  obtain ⟨χ, hχ, hcentral⟩ := hT
  exact (T.arithmeticComap e).isUnitarizable_of_hasUnitaryCentralCharacter
    ⟨HeckeCharacter.comap e χ, (HeckeCharacter.isUnitary_comap_iff e χ).mpr hχ,
      (T.arithmeticComap_hasCentralCharacter_iff e χ).mpr hcentral⟩

end Regular

/-! ### The prime step -/

/-- In prime cyclic degree, the prime orbit realization, the pair count and the reverse
orbit comparison give an actual unitary cusp below, whose singleton has the full orbit as
weak base change and which is weakly induced from the given cusp. -/
theorem exists_weakInduction_of_prime {A : Type uA} {B : Type uB} [Field A] [NumberField A]
    [Field B] [NumberField B] [Algebra A B] [IsGalois A B] [CompactSpace (AdeleQuotient A)]
    [CompactSpace (AdeleQuotient B)]
    (hReal : (Module.finrank A B).Prime → ∀ σ : B ≃ₐ[A] B,
      (∀ τ : B ≃ₐ[A] B, τ ∈ Subgroup.zpowers σ) →
      ∀ (m : ℕ) (T : CuspidalOperatorRealization B m), HasUnitaryCentralCharacter T →
        ¬ T.isoClass.IsGaloisStable σ →
        ∃ (r : ℕ) (S : CuspidalOperatorRealization A r),
          r + 1 = (m + 1) * Module.finrank A B ∧ HasUnitaryCentralCharacter S ∧
          IsobaricData.IsWeakBaseChangeOf.{uA, uB, uP, uQ}
            (IsobaricData.galoisOrbit A (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
            (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)))
    (hPair : ∀ [IsCyclic (B ≃ₐ[A] B)],
      CyclicWeakBaseChangePairMultiplicityOver.{uA, uB, uP, uQ} A B)
    (hOrbit : ∀ [IsCyclic (B ≃ₐ[A] B)] (η : HeckeCharacter A), η.HasNormKernel B →
      ∀ {r m : ℕ} (c : IsoClass A r) (d : IsoClass B m),
        IsoClass.IsFiniteOrderDeterminantTwist η c c →
        IsobaricData.IsWeakBaseChangeOf.{uA, uB, uP, uQ}
          (IsobaricData.galoisOrbit A (PositiveRankCuspidalClass.ofFixedRank d))
          (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)) →
        IsoClass.IsWeakInductionOf.{uA, uB, uP, uQ} c d)
    (hp : (Module.finrank A B).Prime) (σ : B ≃ₐ[A] B)
    (hgen : ∀ τ : B ≃ₐ[A] B, τ ∈ Subgroup.zpowers σ)
    (m : ℕ) (T : CuspidalOperatorRealization B m) (hT : HasUnitaryCentralCharacter T)
    (htriv : ∀ τ : B ≃ₐ[A] B, T.isoClass.IsGaloisStable τ → τ = 1) :
    ∃ (r : ℕ) (S : CuspidalOperatorRealization A r),
      r + 1 = (m + 1) * Module.finrank A B ∧ HasUnitaryCentralCharacter S ∧
      IsobaricData.IsWeakBaseChangeOf.{uA, uB, uP, uQ}
        (IsobaricData.galoisOrbit A (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)) ∧
      IsoClass.IsWeakInductionOf.{uA, uB, uP, uQ} S.isoClass T.isoClass := by
  classical
  have : IsCyclic (B ≃ₐ[A] B) := ⟨⟨σ, hgen⟩⟩
  have horder : orderOf σ = Module.finrank A B :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank A B)
  have hσ : ¬ T.isoClass.IsGaloisStable σ := by
    intro h
    rw [htriv σ h, orderOf_one] at horder
    exact hp.one_lt.ne horder
  obtain ⟨r, S, hrank, hS, hBC⟩ := hReal hp σ hgen m T hT hσ
  obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter A B).1
  let c := PositiveRankCuspidalClass.ofFixedRank S.isoClass
  let lower := IsobaricData.ofCuspidal c
  let orbit := IsobaricData.galoisOrbit A (PositiveRankCuspidalClass.ofFixedRank T.isoClass)
  have hlower : lower.IsUnitary :=
    IsobaricData.isUnitary_ofCuspidal.mpr (S.isUnitarizable_of_hasUnitaryCentralCharacter hS)
  have horbit : orbit.IsUnitary := isUnitary_galoisOrbit T hT
  have horbitCount :
      IsobaricData.equalConstituentPairCount orbit orbit = Module.finrank A B := by
    have hnodup : orbit.Nodup := galoisOrbit_nodup T.isoClass htriv
    have hmap : orbit.map (fun d => orbit.count d) = orbit.map (fun _ => (1 : ℕ)) :=
      Multiset.map_congr rfl fun _ hd => Multiset.count_eq_one_of_mem hnodup hd
    unfold IsobaricData.equalConstituentPairCount
    rw [hmap, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
    simp only [orbit, IsobaricData.galoisOrbit, Multiset.card_map, Finset.card_val,
      Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let finiteOrder (i : ℕ) : (η ^ i).HasFiniteOrder :=
    HeckeCharacter.IsTrivialOnNorm.hasFiniteOrder B (by
      intro x
      rw [ContinuousMonoidHom.pow_apply, hη.isTrivialOnNorm x, one_pow])
  let twist (i : ℕ) := c.determinantTwist (η ^ i) (finiteOrder i)
  have hcount : (∑ i ∈ Finset.range (Module.finrank A B), lower.count (twist i)) =
      Module.finrank A B := by
    have h := hPair η hη lower lower orbit orbit hlower hlower horbit horbit hBC hBC
    dsimp only at h
    rw [horbitCount] at h
    simpa only [lower, IsobaricData.ofCuspidal, IsobaricData.equalConstituentPairCount,
      Multiset.map_singleton, Multiset.sum_singleton] using h
  have hle (j : ℕ) (_ : j ∈ Finset.range (Module.finrank A B)) :
      lower.count (twist j) ≤ 1 :=
    (Multiset.count_le_card _ _).trans_eq (Multiset.card_singleton _)
  have hsum := (Finset.sum_eq_sum_iff_of_le (g := fun _ => (1 : ℕ)) hle).mp
    (by simpa using hcount)
  have hmem : twist 1 ∈ lower := Multiset.count_pos.mp
    (by simp only [hsum 1 (Finset.mem_range.mpr hp.one_lt), Nat.zero_lt_one])
  have hfixed : twist 1 = c := by
    simpa only [lower, IsobaricData.ofCuspidal, Multiset.mem_singleton] using hmem
  have hfinite := hη.isTrivialOnNorm.hasFiniteOrder B
  have hself : S.isoClass.determinantTwist η hfinite = S.isoClass := by
    apply PositiveRankCuspidalClass.ofFixedRank_injective r
    simpa only [twist, c, pow_one, PositiveRankCuspidalClass.determinantTwist_ofFixedRank]
      using hfixed
  have htwist : IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass :=
    (IsoClass.isFiniteOrderDeterminantTwist_iff_eq _ _ η hfinite).mpr hself.symm
  exact ⟨r, S, hrank, hS, hBC, hOrbit η hη S.isoClass T.isoClass htwist hBC⟩

/-! ### Degree one -/

section DegreeOne

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

omit [NumberField F] [NumberField E] in
/-- The finite place of `F` corresponding to a place of `E` under a ring isomorphism
`e : F ≃+* E` agreeing with the algebra map is the place below it. -/
theorem finitePlaceEquiv_eq_under (e : F ≃+* E) (he : ∀ x, e x = algebraMap F E x)
    (u : HeightOneSpectrum (𝓞 E)) : finitePlaceEquiv e u = u.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  ext x
  rw [finitePlaceEquiv_mem, HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have hx : NumberField.RingOfIntegers.mapRingEquiv e x = algebraMap (𝓞 F) (𝓞 E) x :=
    NumberField.RingOfIntegers.ext (he (x : F))
  rw [hx]

/-- In degree one, every finite place above `v` has ramification index one. -/
theorem ramificationIdx_eq_one_of_finrank_eq_one (h : Module.finrank F E = 1)
    (v : HeightOneSpectrum (𝓞 F)) (q : FinitePlacesAbove E v) :
    q.1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := E) v
  rw [h] at hsum
  have hle : q.1.asIdeal.ramificationIdx (𝓞 F) * q.1.asIdeal.inertiaDeg (𝓞 F) ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun r : FinitePlacesAbove E v =>
      r.1.asIdeal.ramificationIdx (𝓞 F) * r.1.asIdeal.inertiaDeg (𝓞 F))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  have he := q.1.asIdeal.ramificationIdx_pos (𝓞 F)
  have hf := q.1.asIdeal.inertiaDeg_pos (𝓞 F)
  have hmul : q.1.asIdeal.ramificationIdx (𝓞 F) * q.1.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    have := Nat.mul_pos he hf
    omega
  exact (mul_eq_one.mp hmul).1

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- In degree one, the pullback of the cusp along the field isomorphism is an actual
unitary weak induction of it. -/
theorem exists_weakInduction_of_finrank_eq_one
    (hAttV : CuspidalSpectralAttachmentExistenceStatement.{uE, uV})
    (hAttW : CuspidalSpectralAttachmentExistenceStatement.{uE, uW})
    (hdeg : Module.finrank F E = 1) (m : ℕ) (T : CuspidalOperatorRealization E m)
    (hT : HasUnitaryCentralCharacter T) :
    ∃ (r : ℕ) (S : CuspidalOperatorRealization F r),
      r + 1 = (m + 1) * Module.finrank F E ∧ HasUnitaryCentralCharacter S ∧
      IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass := by
  classical
  let e : F ≃+* E := RingEquiv.ofBijective (algebraMap F E)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg)
  have he : ∀ x, e x = algebraMap F E x := fun _ => rfl
  obtain ⟨tV, htV⟩ := hAttV E m T
  obtain ⟨tW, htW⟩ := hAttW E m T
  obtain ⟨s, hs, hsEuler⟩ :=
    cuspidalArithmeticSpectralTransport.{uF, uE, uV} F E e m T.isoClass tV htV
  let g : FinitePlace F ≃ FinitePlace E := (finitePlaceEquiv e).symm
  have hgabove (v : FinitePlace F) (w : FinitePlacesAbove E v) : w.1 = g v := by
    refine (Equiv.eq_symm_apply _).mpr ?_
    rw [finitePlaceEquiv_eq_under e he]
    exact finitePlacesAbove_under v w
  have hgunder (v : FinitePlace F) : (g v).under (𝓞 F) = v := by
    rw [← finitePlaceEquiv_eq_under e he]
    exact (finitePlaceEquiv e).apply_symm_apply v
  have htend : Filter.Tendsto g Filter.cofinite Filter.cofinite := g.injective.tendsto_cofinite
  refine ⟨m, T.arithmeticComap e, by rw [hdeg, mul_one],
    arithmeticComapUnitaryCentralCharacter.{uF, uE} F E e m T hT, s, tW, hs, htW,
    by rw [hdeg, mul_one], ?_⟩
  filter_upwards [hsEuler, s.exceptional.eventually_cofinite_notMem,
    htend.eventually tV.exceptional.eventually_cofinite_notMem,
    htend.eventually tW.exceptional.eventually_cofinite_notMem] with v hv hsv hV hW
  have ht : ∀ w : FinitePlacesAbove E v, w.1 ∉ tW.exceptional := fun w => by
    rw [hgabove v w]
    exact hW
  refine ⟨hsv, ht, ramificationIdx_eq_one_of_finrank_eq_one hdeg v, ?_⟩
  let w₀ : FinitePlacesAbove E v := ⟨g v, by
    have h := liesOver_under (K := F) (g v)
    rw [hgunder v] at h
    exact h⟩
  have : Subsingleton (FinitePlacesAbove E v) :=
    ⟨fun a b => Subtype.ext ((hgabove v a).trans (hgabove v b).symm)⟩
  rw [SpectralSystem.inducedEulerPolynomial_of_inertiaDeg_eq_one tW v ht
      (fun w => inertiaDeg_eq_one_of_finrank_eq_one hdeg w.1),
    Fintype.prod_subsingleton _ w₀, hv hsv hV]
  exact congrArg Eigenvalues.eulerPolynomial
    (IsoClass.HasSpectralSystem.eigenvalues_eq htV htW (g v) hV (ht w₀))

end DegreeOne

/-! ### Uniqueness of weak base change -/

section Uniqueness

/-- A rank cast keeps the Euler polynomials. -/
theorem sameEulerPolynomials_cast {I : Type*} {n m : ℕ} (h : n = m) (s : SpectralSystem I n) :
    s.SameEulerPolynomials (h ▸ s : SpectralSystem I m) := by
  subst m
  exact SpectralSystem.sameEulerPolynomials_refl s

variable {K : Type uA} {E : Type uB} [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E]

/-- Two arithmetic weak base changes of one spectral system agree in Euler polynomials
outside a finite set. -/
theorem arithmeticWeakBaseChange_sameEulerPolynomials {n : ℕ}
    {s : SpectralSystem (FinitePlace K) n} {t t' : SpectralSystem (FinitePlace E) n}
    (h : t.IsArithmeticWeakBaseChangeOf s) (h' : t'.IsArithmeticWeakBaseChangeOf s) :
    t.SameEulerPolynomials t' := by
  filter_upwards [tendsto_under_cofinite.eventually h, tendsto_under_cofinite.eventually h']
    with w hw hw'
  intro ht ht'
  let q : FinitePlacesAbove E (w.under (𝓞 K)) := ⟨w, liesOver_under w⟩
  obtain ⟨_, _, _, he⟩ := hw
  obtain ⟨_, _, _, he'⟩ := hw'
  exact congrArg Eigenvalues.eulerPolynomial ((he q).trans (he' q).symm)

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient E)]

omit [NumberField K] [Algebra K E] [CompactSpace (AdeleQuotient K)] in
/-- Euler constituent recovery over `E` identifies isobaric data with attached spectral
systems of the same Euler polynomials. -/
theorem eq_of_attached_sameEulerPolynomials
    (hRec : CuspidalEulerConstituentRecoveryAt.{uB, uQ} E)
    {D D' : IsobaricData E} {s : SpectralSystem (FinitePlace E) D.rank}
    {t : SpectralSystem (FinitePlace E) D'.rank}
    (hs : IsobaricData.HasSpectralSystem.{uB, uQ} D s)
    (ht : IsobaricData.HasSpectralSystem.{uB, uQ} D' t)
    (hst : s.SameEulerPolynomials t) : D = D' := by
  obtain ⟨p, c, hc, a, ha, has⟩ := hs
  obtain ⟨q, d, hd, b, hb, hbt⟩ := ht
  obtain ⟨e, he⟩ := hRec p q c d a b ha hb (has.trans (hst.trans hbt.symm))
  rw [← hc, ← hd]
  simp only [show c = d ∘ e from funext he, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Euler constituent recovery over `E` makes weak base change of isobaric data unique. -/
theorem isWeakBaseChangeOf_unique (hRec : CuspidalEulerConstituentRecoveryAt.{uB, uQ} E)
    {DF : IsobaricData K} {DE DE' : IsobaricData E}
    (h : IsobaricData.IsWeakBaseChangeOf.{uA, uB, uP, uQ} DE DF)
    (h' : IsobaricData.IsWeakBaseChangeOf.{uA, uB, uP, uQ} DE' DF) : DE = DE' := by
  obtain ⟨hn, s, t, hs, ht, hst⟩ := h
  obtain ⟨hm, s', t', hs', ht', hst'⟩ := h'
  have hss' := hs'.sameEulerPolynomials hs
  have hst'' := hst'.of_sameEulerPolynomials hss' (SpectralSystem.sameEulerPolynomials_refl _)
  have he := arithmeticWeakBaseChange_sameEulerPolynomials hst hst''
  exact eq_of_attached_sameEulerPolynomials hRec ht ht'
    ((sameEulerPolynomials_cast hn t).trans (he.trans (sameEulerPolynomials_cast hm t').symm))

end Uniqueness

/-- Stability under a `K`-automorphism is stability under the same automorphism over `F`. -/
theorem isGaloisStable_restrictScalars {F K E : Type*} [Field F] [Field K] [Field E]
    [NumberField E] [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [CompactSpace (AdeleQuotient E)] {m : ℕ} (c : IsoClass E m) (τ : E ≃ₐ[K] E) :
    c.IsGaloisStable (τ.restrictScalars F) ↔ c.IsGaloisStable τ := by
  rw [IsoClass.isGaloisStable_iff, IsoClass.isGaloisStable_iff]
  rfl

/-! ### Induction on the degree -/

/-- The common argument of both reductions, over a fixed lower field `F`: strong induction on
`[E : F]` with the upper field ranging over `Type uE`. The hypotheses over intermediate
fields are required only for fields carrying an algebra over `F`. -/
theorem cyclicRegularInductionExistenceOver_of_inputs {F : Type uF} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)]
    (hRealF : ∀ (E : Type uE) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
      [CompactSpace (AdeleQuotient E)], (Module.finrank F E).Prime → ∀ σ : E ≃ₐ[F] E,
      (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (m : ℕ) (T : CuspidalOperatorRealization E m), HasUnitaryCentralCharacter T →
        ¬ T.isoClass.IsGaloisStable σ →
        ∃ (r : ℕ) (S : CuspidalOperatorRealization F r),
          r + 1 = (m + 1) * Module.finrank F E ∧ HasUnitaryCentralCharacter S ∧
          IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
            (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
            (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)))
    (hRealK : ∀ (K E : Type uE) [Field K] [NumberField K] [Algebra F K] [Field E]
      [NumberField E] [Algebra K E] [IsGalois K E] [CompactSpace (AdeleQuotient K)]
      [CompactSpace (AdeleQuotient E)], (Module.finrank K E).Prime → ∀ σ : E ≃ₐ[K] E,
      (∀ τ : E ≃ₐ[K] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (m : ℕ) (T : CuspidalOperatorRealization E m), HasUnitaryCentralCharacter T →
        ¬ T.isoClass.IsGaloisStable σ →
        ∃ (r : ℕ) (S : CuspidalOperatorRealization K r),
          r + 1 = (m + 1) * Module.finrank K E ∧ HasUnitaryCentralCharacter S ∧
          IsobaricData.IsWeakBaseChangeOf.{uE, uE, uW, uW}
            (IsobaricData.galoisOrbit K (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
            (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)))
    (hPairF : ∀ (E : Type uE) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
      [IsCyclic (E ≃ₐ[F] E)] [CompactSpace (AdeleQuotient E)],
      CyclicWeakBaseChangePairMultiplicityOver.{uF, uE, uV, uW} F E)
    (hPairK : ∀ (K E : Type uE) [Field K] [NumberField K] [Algebra F K] [Field E]
      [NumberField E] [Algebra K E] [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)]
      [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient E)],
      CyclicWeakBaseChangePairMultiplicityOver.{uE, uE, uW, uW} K E)
    (hOrbitF : CyclicOrbitBaseChangeWeakInductionStatement.{uF, uE, uV, uW})
    (hOrbitK : CyclicOrbitBaseChangeWeakInductionStatement.{uE, uE, uW, uW})
    (hEquiv : IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW})
    (hRec : ∀ (E : Type uE) [Field E] [NumberField E] [Algebra F E]
      [CompactSpace (AdeleQuotient E)], CuspidalEulerConstituentRecoveryAt.{uE, uW} E)
    (hTrans : WeakInductionTransitivityStatement.{uF, uE, uE, uV, uW, uW})
    (hAttV : CuspidalSpectralAttachmentExistenceStatement.{uE, uV})
    (hAttW : CuspidalSpectralAttachmentExistenceStatement.{uE, uW})
    (E : Type uE) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient E)] :
    CyclicRegularInductionExistenceOver.{uF, uE, uV, uW} F E := by
  suffices h : ∀ (n : ℕ) (E : Type uE) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
      [CompactSpace (AdeleQuotient E)], Module.finrank F E = n →
      CyclicRegularInductionExistenceOver.{uF, uE, uV, uW} F E from h _ E rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E _ _ _ _ _ hn σ hgen m T hT hreg
  subst hn
  classical
  have horder : orderOf σ = Module.finrank F E :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank F E)
  have htriv : ∀ τ : E ≃ₐ[F] E, T.isoClass.IsGaloisStable τ → τ = 1 :=
    eq_one_of_isGaloisStable σ hgen T.isoClass (by rwa [horder])
  by_cases h1 : Module.finrank F E = 1
  · exact exists_weakInduction_of_finrank_eq_one hAttV hAttW h1 m T hT
  by_cases hprime : (Module.finrank F E).Prime
  · obtain ⟨r, S, hr, hS, -, hInd⟩ :=
      exists_weakInduction_of_prime (hRealF E) (hPairF E) (hOrbitF F E) hprime σ hgen m T hT htriv
    exact ⟨r, S, hr, hS, hInd⟩
  -- Composite degree: the fixed field of a subgroup of prime order.
  have hpos : 0 < Module.finrank F E := Module.finrank_pos
  have h2 : 2 ≤ Module.finrank F E := by omega
  have hp : (Module.finrank F E).minFac.Prime := Nat.minFac_prime h1
  have hpdvd : (Module.finrank F E).minFac ∣ Module.finrank F E := Nat.minFac_dvd _
  let p := (Module.finrank F E).minFac
  let g : E ≃ₐ[F] E := σ ^ (orderOf σ / p)
  have hg : orderOf g = p := orderOf_pow_orderOf_div (by omega) (horder ▸ hpdvd)
  let H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers g
  have hcomm : ∀ a b : E ≃ₐ[F] E, Commute a b := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
    exact Commute.zpow_zpow_self σ i j
  have hH : H.Normal := ⟨fun a ha b => by rw [(hcomm b a).eq, mul_inv_cancel_right]; exact ha⟩
  let K : IntermediateField F E := IntermediateField.fixedField H
  have : IsGalois F K := IsGalois.of_fixedField_normal_subgroup H
  have : CompactSpace (AdeleQuotient K) := compactSpace_adeleQuotient K
  have hKE : Module.finrank K E = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans ((Nat.card_zpowers g).trans hg)
  have htower : Module.finrank F K * Module.finrank K E = Module.finrank F E :=
    Module.finrank_mul_finrank F K E
  have hFKpos : 0 < Module.finrank F K := Module.finrank_pos
  have hFK : Module.finrank F K < Module.finrank F E := by
    rw [← htower, hKE]
    have := hp.two_le
    nlinarith
  -- The prime step for `E/K`.
  have hpK : (Module.finrank K E).Prime := hKE ▸ hp
  have : Fact (Nat.card (E ≃ₐ[K] E)).Prime := ⟨by rw [IsGalois.card_aut_eq_finrank]; exact hpK⟩
  have : IsCyclic (E ≃ₐ[K] E) := isCyclic_of_prime_card rfl
  obtain ⟨σK, hσK⟩ := IsCyclic.exists_generator (α := E ≃ₐ[K] E)
  have htrivK : ∀ τ : E ≃ₐ[K] E, T.isoClass.IsGaloisStable τ → τ = 1 := by
    intro τ hτ
    have h := htriv (τ.restrictScalars F) ((isGaloisStable_restrictScalars T.isoClass τ).mpr hτ)
    ext x
    exact DFunLike.congr_fun h x
  obtain ⟨s, U, hs, hU, hBCK, hIndK⟩ :=
    exists_weakInduction_of_prime (hRealK K E) (hPairK K E) (hOrbitK K E) hpK σK hσK m T hT htrivK
  -- The intermediate cusp is regular for `K/F`.
  have : IsCyclic (E ≃ₐ[F] E) := ⟨⟨σ, hgen⟩⟩
  have : IsCyclic (K ≃ₐ[F] K) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom K)
      (AlgEquiv.restrictNormalHom_surjective (K₁ := K) E)
  obtain ⟨σF, hσF⟩ := IsCyclic.exists_generator (α := K ≃ₐ[F] K)
  let t := PositiveRankCuspidalClass.ofFixedRank T.isoClass
  have htrivU : ∀ ρ : K ≃ₐ[F] K, U.isoClass.IsGaloisStable ρ → ρ = 1 := by
    intro ρ hρ
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := K) E ρ
    have hcompat : ∀ x : K, τ.toRingEquiv (algebraMap K E x) =
        algebraMap K E ((AlgEquiv.restrictNormalHom K τ).toRingEquiv x) :=
      fun x => (AlgEquiv.restrictNormal_commutes τ K x).symm
    have hBC' := hEquiv K E (AlgEquiv.restrictNormalHom K τ).toRingEquiv τ.toRingEquiv
      hcompat _ _ hBCK
    have hlow : ((IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank U.isoClass)).map
        fun c => c.arithmeticComap (AlgEquiv.restrictNormalHom K τ).toRingEquiv.symm) =
        IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank U.isoClass) := by
      simp only [IsobaricData.ofCuspidal, Multiset.map_singleton]
      congr 1
      exact (PositiveRankCuspidalClass.isGaloisStable_iff_galoisConj_ofFixedRank _
        U.isoClass).mp hρ
    rw [hlow] at hBC'
    have heq := isWeakBaseChangeOf_unique (hRec E) hBC' hBCK
    have hmem : t ∈ (IsobaricData.galoisOrbit K t).map
        (fun c => c.arithmeticComap τ.toRingEquiv.symm) := by
      rw [heq]
      exact Multiset.mem_map.mpr ⟨1, Finset.mem_univ_val _,
        PositiveRankCuspidalClass.galoisConj_one _⟩
    obtain ⟨c', hc', hc'eq⟩ := Multiset.mem_map.mp hmem
    obtain ⟨ρ', -, rfl⟩ := Multiset.mem_map.mp hc'
    let μ : E ≃ₐ[F] E := τ * ρ'.restrictScalars F
    have hconj : PositiveRankCuspidalClass.galoisConj μ t =
        (PositiveRankCuspidalClass.galoisConj ρ' t).arithmeticComap τ.toRingEquiv.symm := by
      rw [PositiveRankCuspidalClass.galoisConj_eq_arithmeticComap,
        PositiveRankCuspidalClass.galoisConj_eq_arithmeticComap,
        ← PositiveRankCuspidalClass.arithmeticComap_trans]
      congr 1
    have hμ : μ = 1 := htriv μ
      ((PositiveRankCuspidalClass.isGaloisStable_iff_galoisConj_ofFixedRank μ T.isoClass).mpr
        (hconj.trans hc'eq))
    have hfix : ∀ x : K, τ (algebraMap K E x) = algebraMap K E x := by
      intro x
      have h := DFunLike.congr_fun hμ (algebraMap K E x)
      rwa [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
        AlgEquiv.one_apply] at h
    ext x
    exact (AlgEquiv.restrictNormal_commutes τ K x).trans (hfix x)
  -- Induction hypothesis for `K/F` and composition in the tower.
  have horderF : orderOf σF = Module.finrank F K :=
    (orderOf_eq_card_of_forall_mem_zpowers hσF).trans (IsGalois.card_aut_eq_finrank F K)
  obtain ⟨r, S, hr, hS, hIndF⟩ := ih (Module.finrank F K) hFK K rfl σF hσF s U hU
    (fun i hi0 hi => not_isGaloisStable_pow σF U.isoClass htrivU i hi0 (horderF ▸ hi))
  refine ⟨r, S, ?_, hS, hTrans F K E S.isoClass U.isoClass T.isoClass hIndF hIndK⟩
  rw [hr, hs, mul_assoc, mul_comm (Module.finrank K E), htower]

end CyclicRegularInductionExistence

end Langlands.Automorphic.Unramified

namespace Langlands.Automorphic.Unramified

open CyclicRegularInductionExistence

/-- The exact target `CyclicRegularInductionExistenceReductionStatement`: every premise is
used over arbitrary number fields, at the stated universe levels. -/
theorem cyclicRegularInductionExistenceReduction :
    CyclicRegularInductionExistenceReductionStatement.{uF, uE, uV, uW} := by
  intro hRealF hRealK hPairF hPairK hOrbitF hOrbitK hEquiv hRec hTrans hAttV hAttW
    F E _ _ _ _ _ _ _ _
  exact cyclicRegularInductionExistenceOver_of_inputs
    (fun E => hRealF F E)
    (fun K E => hRealK K E)
    (fun E => hPairF F E)
    (fun K E => hPairK K E)
    hOrbitF hOrbitK hEquiv
    (fun E => hRec E)
    hTrans hAttV hAttW E

end Langlands.Automorphic.Unramified
