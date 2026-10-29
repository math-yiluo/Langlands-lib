import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.Classification.ProductLeviSquareIntegrableSufficiencyProof

/-!
# Product-Levi dual-opposite square-integrability sufficiency

The opposite dual-eigenfunctional form of product-Levi square-integrability
sufficiency follows from its upper generalized-exponent form, as in the
published tempered adapter. Conjugation by the blockwise reversal matrices
turns an upper generalized eigencharacter into the eigencharacter of a nonzero
dual eigenfunctional of the opposite quotient of the reversed refinement. Its
nonpositive within-block prefixes give the weak bound by summation by parts;
strictly negative proper prefixes give the strict bound on tuples whose
absolute values are not constant on some block.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric Finset
open scoped BigOperators

universe uF uV

namespace ProductLeviDualOpposite

variable {L : ℕ}

/-- Strict summation by parts: residuals with strictly negative proper prefix
sums and zero total pair negatively with every nonconstant antitone vector. -/
theorem sum_mul_neg_of_antitone (e v : Fin L → ℝ) (hv : Antitone v)
    (hproper : ∀ i : Fin L, (i : ℕ) + 1 < L →
      ∑ k ∈ univ.filter (fun k => k ≤ i), e k < 0)
    (htot : ∑ k, e k = 0) (hne : ∃ i i', v i ≠ v i') :
    ∑ k, e k * v k < 0 := by
  obtain ⟨i, i', hii'⟩ := hne
  have hL : 2 ≤ L := by
    by_contra h
    apply hii'
    congr 1
    have := i.isLt
    have := i'.isLt
    ext
    omega
  let first : Fin L := ⟨0, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  have hfirst : ∀ k : Fin L, first ≤ k := fun k => Fin.le_def.mpr (Nat.zero_le _)
  have hlast : ∀ k : Fin L, k ≤ last := fun k => Fin.le_def.mpr (by
    have := k.isLt
    simp only [last]
    omega)
  obtain ⟨i₀, hi₀, hmax⟩ := exists_max_image (univ.filter fun k : Fin L => (k : ℕ) + 1 < L)
    (fun i => ∑ k ∈ univ.filter (fun k => k ≤ i), e k)
    ⟨first, by simp only [mem_filter, mem_univ, true_and, first]; omega⟩
  set η := ∑ k ∈ univ.filter (fun k => k ≤ i₀), e k with hηdef
  have hη : η < 0 := hproper i₀ (by simpa using hi₀)
  -- Shift the residuals by `-η` at the first index and `+η` at the last.
  let e' : Fin L → ℝ := fun k => e k - (if k = first then η else 0) + (if k = last then η else 0)
  have hpre_e' : ∀ i, ∑ k ∈ univ.filter (fun k => k ≤ i), e' k =
      ∑ k ∈ univ.filter (fun k => k ≤ i), e k - η + (if i = last then η else 0) := by
    intro i
    simp only [e', sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_filter, mem_univ,
      true_and, ite_eq_left (hfirst i)]
    congr 1
    by_cases hi : i = last
    · rw [ite_eq_left (hi ▸ le_rfl), ite_eq_left hi]
    · rw [ite_eq_right hi, ite_eq_right fun h => hi (le_antisymm (hlast i) h)]
  have htot' : ∑ k, e' k = 0 := by
    simp only [e', sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, htot]
    ring
  have hpre' : ∀ i, ∑ k ∈ univ.filter (fun k => k ≤ i), e' k ≤ 0 := by
    intro i
    rw [hpre_e' i]
    by_cases hi : i = last
    · rw [ite_eq_left hi]
      have hall : univ.filter (fun k : Fin L => k ≤ i) = univ := by
        ext k
        simp only [mem_filter, mem_univ, true_and, iff_true]
        exact hi ▸ hlast k
      rw [hall, htot]
      linarith
    · rw [ite_eq_right hi]
      have hp : (i : ℕ) + 1 < L := by
        have := i.isLt
        have : (i : ℕ) ≠ L - 1 := fun h => hi (Fin.ext h)
        omega
      have := hmax i (by simp only [mem_filter, mem_univ, true_and]; exact hp)
      linarith
  have hweak := ParabolicConeUniqueness.sum_mul_nonpos_of_antitone e' v hv hpre' htot'
  have hexpand : ∑ k, e' k * v k = ∑ k, e k * v k - η * v first + η * v last := by
    simp only [e', add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, ite_mul, zero_mul,
      sum_ite_eq', mem_univ, ite_true]
  have hvfl : v last < v first := by
    have hle : ∀ k, v last ≤ v k ∧ v k ≤ v first := fun k => ⟨hv (hlast k), hv (hfirst k)⟩
    refine lt_of_le_of_ne (hle first).1 fun h => hii' ?_
    have h1 := hle i
    have h2 := hle i'
    linarith
  nlinarith [mul_neg_of_neg_of_pos hη (sub_pos.mpr hvfl)]

end ProductLeviDualOpposite

open ProductLeviDualOpposite in
/-- The upper generalized-exponent form of product-Levi square-integrability
sufficiency implies its opposite dual-eigenfunctional form. -/
theorem glProductLeviDualOppositeSquareIntegrableSufficiency_of_core
    (h : GLProductLeviSquareIntegrableExponentSufficiencyStatement.{uF, uV}) :
    GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn C S ω hirr hadm hω hunit hdual
  refine h p F T n hn C S ω hirr hadm hω hunit ?_
  intro D ψ hψ hgen a ha
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have : IsTopologicalGroup ((C.flatten (reverseRefinement C D)).Levi F.Carrier) :=
    T.leviTopologicalGroup _
  have hgen' := isGeneralizedEigencharacter_reverse T C D S.ρ hgen
  have hadm' : IsAdmissible ((T.normalizedRefinedOppositeJacquet C (reverseRefinement C D)
      S.ρ).comp (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)).toMonoidHom) :=
    isAdmissible_comp_continuousMulEquiv _
      (flattenedLeviEquivContinuous F.Carrier C (reverseRefinement C D))
      (Parabolic.isAdmissible_normalizedRefinedOppositeJacquet F T C (reverseRefinement C D)
        _ S.ρ hadm)
  have hcof : CompactOpenCofinal ((C.flatten (reverseRefinement C D)).Levi F.Carrier) :=
    fun K =>
      let L := T.leviCompactOpen (C.flatten (reverseRefinement C D)) K
        (K.isOpen.mem_nhds K.one_mem)
      ⟨L.1, L.2.1, fun x hx => L.2.2 hx⟩
  obtain ⟨φ, hφ, heig⟩ :=
    DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter _ hadm' hcof
      ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier)
      (fun a => (C.flatten (reverseRefinement C D)).blockScalarLevi_mem_center F.Carrier a)
      _ hgen'
  have hcont : Continuous (MaximalConeAssembly.precomp (M := F.Carrierˣ)
      (reverseLabel C D).symm) := by
    change Continuous fun c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ =>
      fun k => c ((reverseLabel C D).symm k)
    exact continuous_pi fun k => continuous_apply _
  have hψ' : IsOpen ((ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)).ker :
      Set (Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ)) :=
    hψ.preimage hcont
  obtain ⟨s, hs⟩ := T.exists_isRealPartOf _ hψ'
  have heig' : ∀ (b : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ) (v : S),
      φ (T.normalizedRefinedOppositeJacquet C (reverseRefinement C D) S.ρ
          (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
            ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier b))
          (refinedOppositeJacquetMk C (reverseRefinement C D) S.ρ v)) =
        ((ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)) b : ℂ) *
          φ (refinedOppositeJacquetMk C (reverseRefinement C D) S.ρ v) :=
    fun b v => heig b _
  have hpre := hdual (reverseRefinement C D) _ s φ hψ' hφ heig' hs
  have hzero : ∀ j, ∑ i : Fin (D j).length,
      s (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, i⟩) = 0 := by
    intro j
    have := T.sum_fibre_eq_zero_of_unitary C (reverseRefinement C D) S.ρ hω hunit hφ heig' hs j
    rwa [BlockShape.sum_filter_flattenOuter] at this
  have hpos : ∀ k, 0 < T.normalizedAbs (a k : F.Carrier) := fun k =>
    T.normalizedAbs_pos (a k).ne_zero
  have hψa : ψ a = (ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm))
      (a ∘ reverseLabel C D) := by
    change ψ a = ψ ((a ∘ reverseLabel C D) ∘ (reverseLabel C D).symm)
    congr 1
    funext k
    simp
  rw [hψa, hs]
  have hexp : ∏ b, T.normalizedAbs (((a ∘ reverseLabel C D) b : F.Carrierˣ) : F.Carrier) ^ s b =
      Real.exp (∑ b, s b * Real.log (T.normalizedAbs (a (reverseLabel C D b) : F.Carrier))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Function.comp_apply, Real.rpow_def_of_pos (hpos _), mul_comm]
  rw [hexp, Real.exp_le_one_iff, Real.exp_lt_one_iff,
    ← (C.flattenBlockEquiv (reverseRefinement C D)).sum_comp, Fintype.sum_sigma]
  simp only [reverseLabel_apply]
  have hanti : ∀ j : Fin C.length, Antitone fun i : Fin (D j).length =>
      Real.log (T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, Fin.rev i⟩) : F.Carrier)) :=
    fun j i i' hii' => Real.log_le_log (hpos _) (ha j (Fin.rev_le_rev.mpr hii'))
  have hblock : ∀ j : Fin C.length, ∑ i : Fin (D j).length,
      s (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, i⟩) *
        Real.log (T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, Fin.rev i⟩) : F.Carrier)) ≤ 0 :=
    fun j => ParabolicConeUniqueness.sum_mul_nonpos_of_antitone _ _ (hanti j)
      (fun i => (hpre j i).1) (hzero j)
  refine ⟨Finset.sum_nonpos fun j _ => hblock j, ?_⟩
  rintro ⟨j, i, i', hne⟩
  have hj : ∑ k : Fin (D j).length,
      s (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, k⟩) *
        Real.log (T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, Fin.rev k⟩) : F.Carrier)) < 0 := by
    refine sum_mul_neg_of_antitone _ _ (hanti j)
      (fun k hk => (hpre j k).2 hk) (hzero j) ⟨Fin.rev i, Fin.rev i', ?_⟩
    simp only [Fin.rev_rev]
    intro h'
    exact hne (Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos _)) (Set.mem_Ioi.mpr (hpos _)) h')
  calc _ < ∑ _j : Fin C.length, (0 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hblock j) ⟨j, mem_univ _, hj⟩
    _ = 0 := sum_const_zero

/-- Nonpositive within-block prefixes of every opposite Jacquet dual exponent,
strictly negative for every proper prefix, imply square-integrability modulo
the actual centre of the whole product Levi, for every Borel Haar measure. -/
theorem glProductLeviDualOppositeSquareIntegrableSufficiency :
    GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement.{uF, uV} :=
  glProductLeviDualOppositeSquareIntegrableSufficiency_of_core
    glProductLeviSquareIntegrableExponentSufficiency.{uF, uV}

end Langlands
