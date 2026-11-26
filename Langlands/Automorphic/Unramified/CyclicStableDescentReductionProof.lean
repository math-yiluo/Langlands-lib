import Langlands.Automorphic.Unramified.CyclicStableDescentReductionStatement
import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.ArithmeticComapUnitaryCentralCharacterProof
import Langlands.Automorphic.Unramified.IsobaricSpectralUniqueness
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.AdelicFunctoriality.FinitePlaceEquivUnder
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterProof

/-! # The reduction of cyclic stable descent to prime descent

`cyclicStableDescentReduction` proves `CyclicStableDescentReductionStatement`. A unitary
weak descent of a Galois-stable unitary cusp is built by strong induction on the degree,
first for fields in the upper universe and then for the mixed tower, using degree one,
prime descent and the bottom prime step of a composite cyclic extension. Common-fibre
comparison and the self-pair count then classify all cuspidal descents.
-/

noncomputable section

open scoped BigOperators NumberField

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

namespace CyclicStableDescentReduction

/-! ### Comparison of lower attachments -/

section Comparison

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- Two weak base changes to one upper class give the direct residue-degree comparison
of the two lower attachments. The two upper attachments are compared through their
actual presentations of the same class. -/
theorem exists_sameResidueDegreePowers {r : ℕ} {d : IsoClass E r} {c c' : IsoClass F r}
    (h : IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d c)
    (h' : IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d c') :
    ∃ s s' : SpectralSystem (FinitePlace F) (r + 1),
      IsoClass.HasSpectralSystem.{uF, uV} c s ∧ IsoClass.HasSpectralSystem.{uF, uV} c' s' ∧
        SpectralSystem.SameResidueDegreePowers E s s' := by
  obtain ⟨s, a, hs, ha, hsa⟩ := h
  obtain ⟨s', a', hs', ha', hsa'⟩ := h'
  have haa' : a.SameEulerPolynomials a' :=
    Filter.Eventually.of_forall fun w hw hw' =>
      congrArg Eigenvalues.eulerPolynomial (ha.eigenvalues_eq ha' w hw hw')
  exact ⟨s, s', hs, hs', SpectralSystem.SameResidueDegreePowers.of_common_weakBaseChange
    (hsa.of_sameEulerPolynomials (SpectralSystem.sameEulerPolynomials_refl s) haa') hsa'⟩

end Comparison

/-! ### Norm-trivial characters -/

section NormTrivial

variable {F : Type uF} [Field F] [NumberField F] {E : Type uE} [Field E] [NumberField E]
  [Algebra F E]

/-- Powers of a character trivial on norms are trivial on norms. -/
theorem isTrivialOnNorm_pow {χ : HeckeCharacter F} (hχ : χ.IsTrivialOnNorm E) (k : ℕ) :
    (χ ^ k).IsTrivialOnNorm E := by
  intro x
  rw [ContinuousMonoidHom.pow_apply, hχ x, one_pow]

/-- Quotients of characters trivial on norms are trivial on norms. -/
theorem isTrivialOnNorm_mul_inv {χ ψ : HeckeCharacter F} (hχ : χ.IsTrivialOnNorm E)
    (hψ : ψ.IsTrivialOnNorm E) : (χ * ψ⁻¹).IsTrivialOnNorm E := by
  intro x
  change χ (ideleClassNorm (K := F) (L := E) x) * (ψ (ideleClassNorm (K := F) (L := E) x))⁻¹ = 1
  rw [hχ x, hψ x, inv_one, one_mul]

end NormTrivial

/-! ### Exclusion of norm-trivial self-twists -/

section SelfTwist

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

open Classical in
omit [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] [CompactSpace (AdeleQuotient E)] in
/-- Two singleton data have one equal constituent pair or none. -/
theorem equalConstituentPairCount_ofCuspidal (c d : PositiveRankCuspidalClass F) :
    IsobaricData.equalConstituentPairCount (IsobaricData.ofCuspidal c)
      (IsobaricData.ofCuspidal d) = if c = d then 1 else 0 := by
  classical
  unfold IsobaricData.equalConstituentPairCount IsobaricData.ofCuspidal
  rw [Multiset.map_singleton, Multiset.sum_singleton, Multiset.count_singleton]

/-- In a unitary cuspidal weak lift from a unitary cusp, the singleton self-pair count
excludes every nontrivial norm-trivial self-twist of the lower class. -/
theorem eq_one_of_selfTwist
    (hpair : CyclicWeakBaseChangePairMultiplicityOver.{uF, uE, uV, uW} F E)
    {r : ℕ} {S : CuspidalOperatorRealization F r} {T : CuspidalOperatorRealization E r}
    (hS : HasUnitaryCentralCharacter S) (hT : HasUnitaryCentralCharacter T)
    (hST : IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass)
    {χ : HeckeCharacter F} (hχ : χ.IsTrivialOnNorm E)
    (htw : IsoClass.IsFiniteOrderDeterminantTwist χ S.isoClass S.isoClass) : χ = 1 := by
  classical
  obtain ⟨⟨η, hη⟩, hall⟩ := HeckeCharacter.cyclicNormKernelCharacter.{uF, uE} F E
  obtain ⟨i, hi, rfl⟩ := ((hall η hη).2 χ).mp hχ
  suffices hi0 : i = 0 by rw [hi0, pow_zero]
  let c := PositiveRankCuspidalClass.ofFixedRank S.isoClass
  let lower := IsobaricData.ofCuspidal c
  let upper := IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass)
  have hlower : lower.IsUnitary :=
    IsobaricData.isUnitary_ofCuspidal.mpr (S.isUnitarizable_of_hasUnitaryCentralCharacter hS)
  have hupper : upper.IsUnitary :=
    IsobaricData.isUnitary_ofCuspidal.mpr (T.isUnitarizable_of_hasUnitaryCentralCharacter hT)
  have hBC : IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} upper lower :=
    (IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mpr hST
  have h := hpair η hη lower lower upper upper hlower hlower hupper hupper hBC hBC
  dsimp only at h
  have hfo (j : ℕ) : (η ^ j).HasFiniteOrder :=
    (isTrivialOnNorm_pow hη.isTrivialOnNorm j).hasFiniteOrder E
  let g : ℕ → ℕ := fun j => if S.isoClass.determinantTwist (η ^ j) (hfo j) = S.isoClass then 1 else 0
  have hterm (j : ℕ) (hj : (η ^ j).HasFiniteOrder) :
      IsobaricData.equalConstituentPairCount
        (lower.map fun d => PositiveRankCuspidalClass.determinantTwist d (η ^ j) hj) lower =
        g j := by
    change IsobaricData.equalConstituentPairCount
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank
        (S.isoClass.determinantTwist (η ^ j) hj))) (IsobaricData.ofCuspidal c) = g j
    rw [equalConstituentPairCount_ofCuspidal]
    simp only [g, c, (PositiveRankCuspidalClass.ofFixedRank_injective r).eq_iff]
  have hup : IsobaricData.equalConstituentPairCount upper upper = 1 := by
    rw [equalConstituentPairCount_ofCuspidal]
    simp
  rw [hup, Finset.sum_congr rfl fun j _ => hterm j _] at h
  have hg (j : ℕ) (hj : IsoClass.IsFiniteOrderDeterminantTwist (η ^ j) S.isoClass S.isoClass) :
      g j = 1 := by
    have heq := ((IsoClass.isFiniteOrderDeterminantTwist_iff_eq _ _ _ (hfo j)).mp hj).symm
    simp only [g, heq, ↓reduceIte]
  have hg0 : g 0 = 1 :=
    hg 0 (by rw [pow_zero]; exact IsoClass.IsFiniteOrderDeterminantTwist.refl _)
  by_contra hne
  have hsub : ({0, i} : Finset ℕ) ⊆ Finset.range (Module.finrank F E) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_range.mpr Module.finrank_pos
    · rw [Finset.mem_singleton.mp hj]
      exact Finset.mem_range.mpr hi
  have hle := Finset.sum_le_sum_of_subset (f := g) hsub
  rw [h, Finset.sum_pair (Ne.symm hne), hg0, hg i htw] at hle
  omega

end SelfTwist

/-! ### Degree one -/

section DegreeOne

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

omit [NumberField F] [NumberField E] in
/-- The spectrum at equal places, read through two definedness proofs. -/
theorem eigenvalues_congr_place {I : Type*} {n : ℕ} (s : SpectralSystem I n) {u u' : I}
    (h : u = u') (hu : u ∉ s.exceptional) (hu' : u' ∉ s.exceptional) :
    s.eigenvalues u hu = s.eigenvalues u' hu' := by
  subst h
  rfl

/-- In an extension of degree one, every ramification index is one. -/
theorem ramificationIdx_eq_one_of_finrank_eq_one (h : Module.finrank F E = 1)
    (v : FinitePlace F) (w : FinitePlacesAbove E v) :
    w.1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  classical
  have hw : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := E) v
  rw [h] at hsum
  have hle := Finset.single_le_sum (f := fun q : FinitePlacesAbove E v =>
      q.1.asIdeal.ramificationIdx (𝓞 F) * q.1.asIdeal.inertiaDeg (𝓞 F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  rw [hsum] at hle
  have he : 0 < w.1.asIdeal.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal
  have hf : w.1.asIdeal.inertiaDeg (𝓞 F) = 1 := inertiaDeg_eq_one_of_finrank_eq_one h w.1
  have hle' : w.1.asIdeal.ramificationIdx (𝓞 F) * w.1.asIdeal.inertiaDeg (𝓞 F) ≤ 1 := hle
  rw [hf, mul_one] at hle'
  omega

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- In degree one, the arithmetic pullback along the algebra isomorphism is an actual
weak descent. Its lower attachment is transported from an upper one, and the two
upper attachments agree outside their exceptional sets. -/
theorem isWeakBaseChangeOf_arithmeticComap_of_finrank_eq_one
    (hattV : CuspidalSpectralAttachmentExistenceStatement.{uE, uV})
    (hattW : CuspidalSpectralAttachmentExistenceStatement.{uE, uW})
    (hcomap : CuspidalSpectralArithmeticComapStatement.{uF, uE, uV})
    (hdeg : Module.finrank F E = 1) (e : F ≃+* E) (he : ∀ x, e x = algebraMap F E x)
    {r : ℕ} (T : CuspidalOperatorRealization E r) :
    IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass
      (T.arithmeticComap e).isoClass := by
  obtain ⟨s₀, hs₀⟩ := hattV E r T
  obtain ⟨t, ht⟩ := hattW E r T
  have hs := hcomap F E e r T.isoClass s₀ hs₀
  refine ⟨s₀.reindex (finitePlaceEquiv e), t, hs, ht, ?_⟩
  have hplace (v : FinitePlace F) (w : FinitePlacesAbove E v) : finitePlaceEquiv e w.1 = v := by
    have hu := finitePlaceEquiv_under (L := E) e (fun x => by
      rw [he, Algebra.algebraMap_self, RingHom.id_apply]) w.1
    refine Eq.trans ?_ (hu.trans (finitePlacesAbove_under v w))
    congr 1
  filter_upwards [(s₀.reindex (finitePlaceEquiv e)).exceptional.eventually_cofinite_notMem,
    (t.exceptional.map (finitePlaceEquiv e).toEmbedding).eventually_cofinite_notMem]
    with v hv hvt
  have htw (w : FinitePlacesAbove E v) : w.1 ∉ t.exceptional := by
    intro hmem
    apply hvt
    rw [← hplace v w]
    exact Finset.mem_map_of_mem _ hmem
  have hv₀ : (finitePlaceEquiv e).symm v ∉ s₀.exceptional := fun hmem =>
    hv (Finset.mem_map.mpr ⟨_, hmem, Equiv.apply_symm_apply _ v⟩)
  refine ⟨hv, htw, fun w => ramificationIdx_eq_one_of_finrank_eq_one hdeg v w, fun w => ?_⟩
  rw [inertiaDeg_eq_one_of_finrank_eq_one hdeg w.1, Eigenvalues.power_one]
  have hw : w.1 = (finitePlaceEquiv e).symm v := (Equiv.eq_symm_apply _).mpr (hplace v w)
  have htv : (finitePlaceEquiv e).symm v ∉ t.exceptional := hw ▸ htw w
  calc t.eigenvalues w.1 (htw w) = t.eigenvalues ((finitePlaceEquiv e).symm v) htv :=
        eigenvalues_congr_place t hw _ _
    _ = s₀.eigenvalues ((finitePlaceEquiv e).symm v) hv₀ :=
        (hs₀.eigenvalues_eq ht _ hv₀ htv).symm
    _ = (s₀.reindex (finitePlaceEquiv e)).eigenvalues v hv := rfl

end DegreeOne

/-! ### The bottom prime step of a cyclic tower -/

section Tower

/-- Stability under an automorphism gives stability under its powers. -/
theorem isGaloisStable_pow {K : Type*} {F : Type*} [Field K] [NumberField K] [Field F]
    [Algebra F K] [CompactSpace (AdeleQuotient K)] {r : ℕ} {σ : K ≃ₐ[F] K}
    {c : IsoClass K r} (h : c.IsGaloisStable σ) (k : ℕ) : c.IsGaloisStable (σ ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using IsoClass.isGaloisStable_one c
  | succ k ih => simpa only [pow_succ'] using h.mul ih

/-- The composite step: in a tower `F ⊆ K ⊆ E` with `K/F` cyclic of prime degree,
a unitary weak descent of a `σ`-stable unitary cusp from `E` to `K` is stable under
the generator of `K/F`, and its prime descent is a weak descent from `E` to `F`. -/
theorem exists_descent_of_tower
    (hPD : CyclicPrimeStableCuspidalDescentStatement.{uF, uE, uV, uW})
    (hObs : CyclicPrimeTwistedCuspidalObstructionStatement.{uF, uE})
    (hRes : HeckeCharacter.CyclicPrimeNormCharacterRestrictionStatement.{uF, uE, uE})
    (hTower : IsobaricWeakBaseChangeTowerStatement.{uF, uE, uE, uV, uW, uW})
    (hEquiv : IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW})
    (hTwist : CuspidalDeterminantTwistArithmeticComapStatement.{uE, uE})
    (hPair : CyclicWeakBaseChangePairMultiplicityStatement.{uE, uE, uW, uW})
    (hFib : CyclicCuspidalFiberStatement.{uE, uE, uW, uW})
    {F : Type uF} {K : Type uE} {E : Type uE} [Field F] [NumberField F] [Field K]
    [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [IsGalois F K] [IsGalois K E] [IsGalois F E]
    [IsCyclic (K ≃ₐ[F] K)] [IsCyclic (E ≃ₐ[K] E)] [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    [CompactSpace (AdeleQuotient E)]
    (hp : (Module.finrank F K).Prime)
    (τ : K ≃ₐ[F] K) (hτ : ∀ ρ : K ≃ₐ[F] K, ρ ∈ Subgroup.zpowers τ)
    (σ : E ≃ₐ[F] E) (hστ : ∀ x : K, σ (algebraMap K E x) = algebraMap K E (τ x))
    {r : ℕ} (T : CuspidalOperatorRealization E r) (hT : HasUnitaryCentralCharacter T)
    (hσT : T.isoClass.IsGaloisStable σ)
    (S : CuspidalOperatorRealization K r) (hS : HasUnitaryCentralCharacter S)
    (hST : IsoClass.IsWeakBaseChangeOf.{uE, uE, uW, uW} T.isoClass S.isoClass) :
    ∃ S₀ : CuspidalOperatorRealization F r, HasUnitaryCentralCharacter S₀ ∧
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S₀.isoClass := by
  -- The conjugate of `S` by `τ` is again a weak descent of `T`.
  have hconj : IsoClass.IsWeakBaseChangeOf.{uE, uE, uW, uW} T.isoClass
      (IsoClass.galoisConj τ S.isoClass) := by
    have h := hEquiv K E τ.toRingEquiv σ.toRingEquiv (fun x => hστ x) _ _
      ((IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mpr hST)
    have hT' : T.isoClass.arithmeticComap σ.toRingEquiv.symm = T.isoClass :=
      (IsoClass.isGaloisStable_iff σ _).mp hσT
    have e₁ : (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).map
        (fun c => c.arithmeticComap σ.toRingEquiv.symm) =
        IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass) := by
      rw [IsobaricData.ofCuspidal, Multiset.map_singleton,
        PositiveRankCuspidalClass.arithmeticComap_ofFixedRank, hT']
    have e₂ : (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)).map
        (fun c => c.arithmeticComap τ.toRingEquiv.symm) =
        IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank
          (IsoClass.galoisConj τ S.isoClass)) := rfl
    rw [e₁, e₂] at h
    exact (IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mp h
  -- Common-fibre comparison gives a norm-trivial twist under `τ`.
  obtain ⟨s, s', hs, hs', hsame⟩ := exists_sameResidueDegreePowers hST hconj
  obtain ⟨χ, hχnorm, hχtw⟩ :=
    hFib K E r S.isoClass (IsoClass.galoisConj τ S.isoClass) s s' hs hs' hsame
  have hres := hRes F K E hp χ hχnorm
  -- Iterating the conjugation relation.
  have hiter (k : ℕ) : IsoClass.IsFiniteOrderDeterminantTwist (χ ^ k) S.isoClass
      (IsoClass.galoisConj (τ ^ k) S.isoClass) := by
    induction k with
    | zero =>
      simpa only [pow_zero, IsoClass.galoisConj_one] using
        IsoClass.IsFiniteOrderDeterminantTwist.refl S.isoClass
    | succ k ih =>
      have h₁ := hTwist K K τ.toRingEquiv.symm r S.isoClass
        (IsoClass.galoisConj (τ ^ k) S.isoClass) (χ ^ k) ih
      have hinv : HeckeCharacter.comap τ.toRingEquiv.symm (χ ^ k) = χ ^ k := by
        rw [HeckeCharacter.comap_pow]
        exact congrArg (· ^ k) (hres.1 τ.symm)
      rw [hinv] at h₁
      rw [pow_succ', pow_succ', IsoClass.galoisConj_mul]
      exact hχtw.trans h₁
  have hτp : τ ^ Module.finrank F K = 1 := by
    rw [← IsGalois.card_aut_eq_finrank F K]
    exact pow_card_eq_one'
  have hself : IsoClass.IsFiniteOrderDeterminantTwist (χ ^ Module.finrank F K)
      S.isoClass S.isoClass := by
    simpa only [hτp, IsoClass.galoisConj_one] using hiter (Module.finrank F K)
  -- The self-pair count over `E/K` and the prime obstruction force `χ = 1`.
  have hχp : χ ^ Module.finrank F K = 1 :=
    eq_one_of_selfTwist (hPair K E) hS hT hST (isTrivialOnNorm_pow hχnorm _) hself
  have hχ1 : χ = 1 := by
    by_contra hne
    exact hObs F K hp τ hτ χ (hχnorm.hasFiniteOrder E) (hres.2 hχp hne) r S hχtw
  have hstable : S.isoClass.IsGaloisStable τ := by
    rw [hχ1] at hχtw
    exact (IsoClass.isGaloisStable_iff τ _).mpr
      ((IsoClass.isFiniteOrderDeterminantTwist_one_iff _ _).mp hχtw).symm
  -- Prime descent and transitivity of weak base change.
  obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter.{uF, uE} F K).1
  obtain ⟨S₀, hS₀, h₀⟩ := hPD F K hp τ hτ η hη r S hS hstable
  refine ⟨S₀, hS₀, ?_⟩
  exact (IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mp
    (hTower F K E _ _ _ ((IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mpr h₀)
      ((IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff _ _).mpr hST))

end Tower

/-! ### Existence of a unitary weak descent -/

section Existence

/-- One step of the degree induction: degree one, prime degree, and composite degree
through the bottom prime step, with the descent for the top step supplied. -/
theorem exists_descent_step
    (hPD : CyclicPrimeStableCuspidalDescentStatement.{uF, uE, uV, uW})
    (hObs : CyclicPrimeTwistedCuspidalObstructionStatement.{uF, uE})
    (hRes : HeckeCharacter.CyclicPrimeNormCharacterRestrictionStatement.{uF, uE, uE})
    (hTower : IsobaricWeakBaseChangeTowerStatement.{uF, uE, uE, uV, uW, uW})
    (hEquiv : IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW})
    (hTwist : CuspidalDeterminantTwistArithmeticComapStatement.{uE, uE})
    (hPair : CyclicWeakBaseChangePairMultiplicityStatement.{uE, uE, uW, uW})
    (hFib : CyclicCuspidalFiberStatement.{uE, uE, uW, uW})
    (hattV : CuspidalSpectralAttachmentExistenceStatement.{uE, uV})
    (hattW : CuspidalSpectralAttachmentExistenceStatement.{uE, uW})
    (hcomap : CuspidalSpectralArithmeticComapStatement.{uF, uE, uV})
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    (ih : ∀ (K : Type uE) [Field K] [NumberField K] [Algebra K E] [IsGalois K E]
      [CompactSpace (AdeleQuotient K)], Module.finrank K E < Module.finrank F E →
      ∀ σ' : E ≃ₐ[K] E, (∀ τ : E ≃ₐ[K] E, τ ∈ Subgroup.zpowers σ') →
      ∀ (r : ℕ) (T : CuspidalOperatorRealization E r), HasUnitaryCentralCharacter T →
        T.isoClass.IsGaloisStable σ' →
        ∃ S : CuspidalOperatorRealization K r, HasUnitaryCentralCharacter S ∧
          IsoClass.IsWeakBaseChangeOf.{uE, uE, uW, uW} T.isoClass S.isoClass)
    {r : ℕ} (T : CuspidalOperatorRealization E r) (hT : HasUnitaryCentralCharacter T)
    (hσT : T.isoClass.IsGaloisStable σ) :
    ∃ S : CuspidalOperatorRealization F r, HasUnitaryCentralCharacter S ∧
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass := by
  classical
  let _ : IsCyclic (E ≃ₐ[F] E) := ⟨⟨σ, hgen⟩⟩
  by_cases h1 : Module.finrank F E = 1
  · -- Degree one: transport across the algebra isomorphism.
    let e : F ≃+* E := RingEquiv.ofBijective (algebraMap F E)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1)
    exact ⟨T.arithmeticComap e, arithmeticComapUnitaryCentralCharacter F E e r T hT,
      isWeakBaseChangeOf_arithmeticComap_of_finrank_eq_one hattV hattW hcomap h1 e
        (fun _ => rfl) T⟩
  by_cases hprime : (Module.finrank F E).Prime
  · -- Prime degree.
    obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter.{uF, uE} F E).1
    exact hPD F E hprime σ hgen η hη r T hT hσT
  -- Composite degree: the bottom prime step `K/F`.
  have hnpos : 0 < Module.finrank F E := Module.finrank_pos
  have hp : (Module.finrank F E).minFac.Prime := Nat.minFac_prime h1
  have hpn : (Module.finrank F E).minFac ∣ Module.finrank F E := Nat.minFac_dvd _
  have horder : orderOf σ = Module.finrank F E :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank F E)
  have hcomm (a b : E ≃ₐ[F] E) : a * b = b * a := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
    exact ((Commute.refl σ).zpow_zpow i j).eq
  let H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers (σ ^ (Module.finrank F E).minFac)
  have hHnormal : H.Normal := ⟨fun a ha g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  let K : IntermediateField F E := IntermediateField.fixedField H
  have : IsGalois F K := IsGalois.of_fixedField_normal_subgroup H
  have : CompactSpace (AdeleQuotient K) := compactSpace_adeleQuotient K
  have hKE : Module.finrank K E = Module.finrank F E / (Module.finrank F E).minFac := by
    change Module.finrank (IntermediateField.fixedField H) E = _
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers,
      orderOf_pow_of_dvd hp.ne_zero (horder ▸ hpn), horder]
  have hq : 0 < Module.finrank F E / (Module.finrank F E).minFac :=
    Nat.div_pos (Nat.le_of_dvd hnpos hpn) hp.pos
  have hFK : Module.finrank F K = (Module.finrank F E).minFac := by
    have hmul := Module.finrank_mul_finrank F K E
    rw [hKE] at hmul
    exact Nat.eq_of_mul_eq_mul_right hq (hmul.trans (Nat.mul_div_cancel' hpn).symm)
  have hlt : Module.finrank K E < Module.finrank F E := by
    rw [hKE]
    exact Nat.div_lt_self hnpos hp.one_lt
  -- The generator of `E/K`.
  let σK : E ≃ₐ[K] E := IntermediateField.subgroupEquivAlgEquiv H
    ⟨σ ^ (Module.finrank F E).minFac, Subgroup.mem_zpowers _⟩
  have hσK (ρ : E ≃ₐ[K] E) : ρ ∈ Subgroup.zpowers σK := by
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.mp ((IntermediateField.subgroupEquivAlgEquiv H).symm ρ).2
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hpow : (⟨σ ^ (Module.finrank F E).minFac, Subgroup.mem_zpowers _⟩ : H) ^ k =
        (IntermediateField.subgroupEquivAlgEquiv H).symm ρ :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
    change IntermediateField.subgroupEquivAlgEquiv H _ ^ k = ρ
    rw [← map_zpow, hpow, MulEquiv.apply_symm_apply]
  have hσKT : T.isoClass.IsGaloisStable σK := by
    have hring : σK.toRingEquiv = (σ ^ (Module.finrank F E).minFac).toRingEquiv :=
      RingEquiv.ext fun _ => rfl
    rw [IsoClass.isGaloisStable_iff]
    change T.isoClass.arithmeticComap σK.toRingEquiv.symm = T.isoClass
    rw [hring]
    exact (IsoClass.isGaloisStable_iff _ _).mp (isGaloisStable_pow hσT _)
  -- The generator of `K/F`.
  let τ : K ≃ₐ[F] K := σ.restrictNormal K
  have hτ (ρ : K ≃ₐ[F] K) : ρ ∈ Subgroup.zpowers τ := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := K) E ρ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen g)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, (map_zpow (AlgEquiv.restrictNormalHom K) σ k).symm⟩
  have hστ (x : K) : σ (algebraMap K E x) = algebraMap K E (τ x) :=
    (AlgEquiv.restrictNormal_commutes σ K x).symm
  let _ : IsCyclic (K ≃ₐ[F] K) := ⟨⟨τ, hτ⟩⟩
  let _ : IsCyclic (E ≃ₐ[K] E) := ⟨⟨σK, hσK⟩⟩
  obtain ⟨S, hS, hST⟩ := ih K hlt σK hσK r T hT hσKT
  exact exists_descent_of_tower hPD hObs hRes hTower hEquiv hTwist hPair hFib
    (hFK ▸ hp) τ hτ σ hστ T hT hσT S hS hST

/-- Strong induction on the degree for fields in the upper universe. -/
theorem exists_descent_same
    (hPD : CyclicPrimeStableCuspidalDescentStatement.{uE, uE, uW, uW})
    (hObs : CyclicPrimeTwistedCuspidalObstructionStatement.{uE, uE})
    (hRes : HeckeCharacter.CyclicPrimeNormCharacterRestrictionStatement.{uE, uE, uE})
    (hTower : IsobaricWeakBaseChangeTowerStatement.{uE, uE, uE, uW, uW, uW})
    (hEquiv : IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW})
    (hTwist : CuspidalDeterminantTwistArithmeticComapStatement.{uE, uE})
    (hPair : CyclicWeakBaseChangePairMultiplicityStatement.{uE, uE, uW, uW})
    (hFib : CyclicCuspidalFiberStatement.{uE, uE, uW, uW})
    (hattW : CuspidalSpectralAttachmentExistenceStatement.{uE, uW})
    (hcomap : CuspidalSpectralArithmeticComapStatement.{uE, uE, uW}) (n : ℕ) :
    ∀ (F : Type uE) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
      [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
      [CompactSpace (AdeleQuotient E)], Module.finrank F E = n →
      ∀ σ : E ≃ₐ[F] E, (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (r : ℕ) (T : CuspidalOperatorRealization E r), HasUnitaryCentralCharacter T →
        T.isoClass.IsGaloisStable σ →
        ∃ S : CuspidalOperatorRealization F r, HasUnitaryCentralCharacter S ∧
          IsoClass.IsWeakBaseChangeOf.{uE, uE, uW, uW} T.isoClass S.isoClass := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F E _ _ _ _ _ _ _ _ hn σ hgen r T hT hσT
    refine exists_descent_step hPD hObs hRes hTower hEquiv hTwist hPair hFib hattW hattW hcomap
      σ hgen ?_ T hT hσT
    intro K _ _ _ _ _ hlt σ' hσ' r' T' hT' hσT'
    exact ih _ (hn ▸ hlt) K E rfl σ' hσ' r' T' hT' hσT'

end Existence

end CyclicStableDescentReduction

open CyclicStableDescentReduction in
/-- Prime descent, the prime twisted-cusp obstruction, the weak-transfer, fibre, pair and
character inputs imply the exact cyclic stable descent proposition. -/
theorem cyclicStableDescentReduction :
    CyclicStableDescentReductionStatement.{uF, uE, uV, uW} := by
  intro hPD hPD' hObs hObs' hPair hPair' hFib hFib' hRes hRes' hTower hTower' hEquiv hTwist
    hNormTwist hattV hattW hcomap hcomap' F E _ _ _ _ _ _ _ _ σ hgen η hη r T hT hσT
  let _ : IsCyclic (E ≃ₐ[F] E) := ⟨⟨σ, hgen⟩⟩
  -- A unitary lower cuspidal realization lifting to `T`.
  obtain ⟨S, hS, hST⟩ := exists_descent_step hPD hObs hRes hTower hEquiv hTwist hPair' hFib'
    hattV hattW hcomap σ hgen
    (fun K _ _ _ _ _ _ σ' hσ' r' T' hT' hσT' =>
      exists_descent_same hPD' hObs' hRes' hTower' hEquiv hTwist hPair' hFib' hattW hcomap'
        (Module.finrank K E) K E rfl σ' hσ' r' T' hT' hσT')
    T hT hσT
  obtain ⟨horder, hall⟩ := (HeckeCharacter.cyclicNormKernelCharacter.{uF, uE} F E).2 η hη
  have hnorm (i : ℕ) : (η ^ i).IsTrivialOnNorm E := isTrivialOnNorm_pow hη.isTrivialOnNorm i
  refine ⟨S.isoClass, hST, fun i _ => ⟨_,
    IsoClass.isFiniteOrderDeterminantTwist_determinantTwist _ _ ((hnorm i).hasFiniteOrder E)⟩,
    fun c' => ⟨fun hc' => ?_, fun ⟨i, _, htw⟩ => hNormTwist F E r _ _ _ _ (hnorm i) htw hST⟩,
    ?_⟩
  · -- Every lower cuspidal class lifting to `T` is a norm-trivial twist.
    obtain ⟨s, s', hs, hs', hsame⟩ := exists_sameResidueDegreePowers hST hc'
    obtain ⟨χ, hχ, htw⟩ := hFib F E r _ _ s s' hs hs' hsame
    obtain ⟨i, hi, rfl⟩ := (hall χ).mp hχ
    exact ⟨i, hi, htw⟩
  · -- The twists by distinct powers are distinct.
    intro i j c' hi hj hci hcj
    have hself := hci.trans hcj.symm
    have h1 := eq_one_of_selfTwist (hPair F E) hS hT hST
      (isTrivialOnNorm_mul_inv (hnorm i) (hnorm j)) hself
    have heq : η ^ i = η ^ j := mul_inv_eq_one.mp h1
    have key (a b : ℕ) (hab : a ≤ b) (hb : b < Module.finrank F E) (h : η ^ a = η ^ b) :
        a = b := by
      have hpow : η ^ (b - a) = 1 := by
        rw [pow_sub η hab, h, mul_inv_cancel]
      have hdvd := orderOf_dvd_of_pow_eq_one hpow
      rw [horder] at hdvd
      have hzero : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    rcases le_total i j with h | h
    · exact key i j h hj heq
    · exact (key j i h hi heq.symm).symm

end Langlands.Automorphic.Unramified
