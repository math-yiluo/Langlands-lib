import Langlands.GaloisCohomology.Global.Units.DivisorMap

/-!
# Capitulation of divisors in `K_S`

Let `ℓ` be a prime such that `S` contains the places above `ℓ`, and `Ω` separably closed. Every
divisor of `K_S` prime to `S` becomes, after multiplication by an integer prime to `ℓ`, the divisor
of a unit of `K_S` (`exists_coprime_nsmul_eq_unitsDivisor`): the `ℓ`-primary part of the class
group of `K_S` outside `S` vanishes.

The proof reduces to the divisor `w` of a single place of a finite Galois subextension `L ⊆ K_S`
(the indicator functions `zuInd`). With `h_L = ℓ^a N`, `ℓ ∤ N`, the class number of `L`, `w^{h_L} = (π)`;
an `ℓ^a`-th root `α` of `π` generates an extension of `L` unramified at the places prime to `ℓ` at
which `ℓ^a` divides the valuation of `π`, that is at all places outside `S`
(`mem_maximalUnramifiedOutside_of_pow_eq_level`); so `α ∈ K_S`, and the divisor of `α` is `N w` up
to sign. A general divisor is an integral combination of translates of these
(`good_single_of_base`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Kummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- If `n` is invertible outside `S` and divides the valuations of `a ∈ Eˣ` at all places outside
`S` of a finite subextension `E ⊆ K_S` of `Ω`, every `n`-th root of `a` in `Ω` lies in `K_S`. -/
theorem mem_maximalUnramifiedOutside_of_pow_eq_of_dvd {E : IntermediateField K Ω}
    [FiniteDimensional K E] [NumberField E] (hE : E ≤ maximalUnramifiedOutside K Ω S) {n : ℕ}
    (hn : n ≠ 0) (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K) ∉ v.asIdeal) (a : Eˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) ∉ S →
      (n : ℤ) ∣ WithZero.log (w.valuation E (a : E)))
    {α : Ω} (hα : α ^ n = ((a : E) : Ω)) :
    α ∈ maximalUnramifiedOutside K Ω S := by
  have hEu : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le S).2 hE
  have hα' : α ^ n = algebraMap E Ω (a : E) := hα
  have hαint : IsIntegral E α := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hα']
    exact isIntegral_algebraMap
  let M : IntermediateField E Ω := IntermediateField.adjoin E {α}
  have : FiniteDimensional E M := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField M := NumberField.of_module_finite E M
  have hβ : IntermediateField.AdjoinSimple.gen E α ^ n = algebraMap E M (a : E) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hα']
    rfl
  have hMu : IsUnramifiedOutside (finitePlacesAbove E S) M := by
    intro w hw
    have hv : w.under (𝓞 K) ∉ S := fun h => hw (mem_finitePlacesAbove_iff_under.2 h)
    refine isUnramifiedIn_of_pow_eq a hβ (adjoin_gen_eq_top E α) w ?_ (ha w hv)
    intro hmem
    apply hnS _ hv
    change ((n : ℕ) : 𝓞 K) ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 E)) w.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hmem
  have hMF := (isUnramifiedOutside_restrictScalars_iff S hEu M).2 hMu
  have : FiniteDimensional K (M.restrictScalars K) := FiniteDimensional.trans K E M
  exact le_maximalUnramifiedOutside S hMF (IntermediateField.mem_adjoin_simple_self E α)

end Kummer

section Good

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

/-- A function `{v ∉ S} → G_S → ℤ` is *capitulating* (for `ℓ`) if some multiple of it by an integer
prime to `ℓ` is the divisor function of a unit of `K_S`. -/
def IsCapitulating (ℓ : ℕ) (f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} →
    GaloisGroupUnramifiedOutside K Ω S → ℤ) : Prop :=
  ∃ N : ℕ, N.Coprime ℓ ∧ ∃ y : (maximalUnramifiedOutside K Ω S)ˣ, ∀ v g,
    sOrder S ι v.1 (galUnitsHom K _ g y) = N * f v g

theorem isCapitulating_zero (ℓ : ℕ) : IsCapitulating S ι ℓ 0 :=
  ⟨1, Nat.coprime_one_left ℓ, 1, fun v x => by
    rw [map_one, sOrder_one ι v.2, Pi.zero_apply, Pi.zero_apply, mul_zero]⟩

theorem IsCapitulating.add {ℓ : ℕ} {f g : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} →
    GaloisGroupUnramifiedOutside K Ω S → ℤ}
    (hf : IsCapitulating S ι ℓ f) (hg : IsCapitulating S ι ℓ g) : IsCapitulating S ι ℓ (f + g) := by
  obtain ⟨N₁, h₁, y₁, hy₁⟩ := hf
  obtain ⟨N₂, h₂, y₂, hy₂⟩ := hg
  refine ⟨N₁ * N₂, Nat.Coprime.mul_left h₁ h₂, y₁ ^ N₂ * y₂ ^ N₁, fun v x => ?_⟩
  have hp : ∀ (y : (maximalUnramifiedOutside K Ω S)ˣ) (m : ℕ),
      sOrder S ι v.1 (y ^ m) = m * sOrder S ι v.1 y := by
    intro y m
    induction m with
    | zero => simp [sOrder_one ι v.2]
    | succ m ih => rw [pow_succ, sOrder_mul ι v.2, ih]; push_cast; ring
  rw [map_mul, map_pow, map_pow, sOrder_mul ι v.2, hp, hp, hy₁, hy₂, Pi.add_apply, Pi.add_apply]
  push_cast
  ring

theorem IsCapitulating.zsmul {ℓ : ℕ} {f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} →
    GaloisGroupUnramifiedOutside K Ω S → ℤ} (hf : IsCapitulating S ι ℓ f) (c : ℤ) :
    IsCapitulating S ι ℓ (c • f) := by
  obtain ⟨N, h, y, hy⟩ := hf
  refine ⟨N, h, y ^ c, fun v x => ?_⟩
  have hz : ∀ (y : (maximalUnramifiedOutside K Ω S)ˣ) (m : ℤ),
      sOrder S ι v.1 (y ^ m) = m * sOrder S ι v.1 y := by
    intro y m
    have hp : ∀ (m : ℕ), sOrder S ι v.1 (y ^ m) = m * sOrder S ι v.1 y := by
      intro m
      induction m with
      | zero => simp [sOrder_one ι v.2]
      | succ m ih => rw [pow_succ, sOrder_mul ι v.2, ih]; push_cast; ring
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · rw [zpow_natCast, hp]
    · have h1 := sOrder_mul ι v.2 (y ^ k) (y ^ (-(k : ℤ)))
      rw [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, sOrder_one ι v.2] at h1
      rw [zpow_natCast, hp] at h1
      linarith
  rw [map_zpow, hz, hy]
  change c * (N * f v x) = N * (c * f v x)
  ring

theorem isCapitulating_sum {ℓ : ℕ} {J : Type*} (T : Finset J)
    (f : J → {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
    (hf : ∀ i ∈ T, IsCapitulating S ι ℓ (f i)) : IsCapitulating S ι ℓ (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isCapitulating_zero S ι ℓ
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a T)).add S ι
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem IsCapitulating.translate {ℓ : ℕ}
    {f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ}
    (hf : IsCapitulating S ι ℓ f) (g : GaloisGroupUnramifiedOutside K Ω S) :
    IsCapitulating S ι ℓ (fun v x => f v (x * g)) := by
  obtain ⟨N, h, y, hy⟩ := hf
  refine ⟨N, h, galUnitsHom K _ g y, fun v x => ?_⟩
  rw [← hy v (x * g), map_mul, Monoid.End.coe_mul, Function.comp_apply]

/-- The image of the decomposition map of `ι` at `v`, a subgroup of `G_S`. -/
abbrev decompositionSubgroup (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S) :=
  (localizationHom ι S v : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
    GaloisGroupUnramifiedOutside K Ω S).range

open Classical in
/-- The indicator function of the double coset `Z_v · U` (`Z_v` the decomposition subgroup). -/
def zuInd (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (g : GaloisGroupUnramifiedOutside K Ω S) :
    ℤ :=
  if ∃ z ∈ decompositionSubgroup S ι v.1, ∃ u ∈ U, g = z * u then 1 else 0

open Classical in
/-- If the indicator function of `Z_v U` (at the place `v`) is capitulating, so is every function at
`v` which is left `Z_v`-invariant and right `U`-invariant, for `U` open and normal. -/
theorem isCapitulating_single_of_base {ℓ : ℕ} (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) [hUn : U.Normal]
    (hU : IsOpen (U : Set (GaloisGroupUnramifiedOutside K Ω S)))
    (hbase : IsCapitulating S ι ℓ (Pi.single v (zuInd S ι v U)))
    (φ : GaloisGroupUnramifiedOutside K Ω S → ℤ) (hφU : ∀ x, ∀ u ∈ U, φ (x * u) = φ x)
    (hφZ : ∀ z ∈ decompositionSubgroup S ι v.1, ∀ x, φ (z * x) = φ x) :
    IsCapitulating S ι ℓ (Pi.single v φ) := by
  have : Finite (GaloisGroupUnramifiedOutside K Ω S ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have := Fintype.ofFinite (GaloisGroupUnramifiedOutside K Ω S ⧸ U)
  set Z := decompositionSubgroup S ι v.1 with hZ
  suffices key : ∀ n : ℕ, ∀ φ : GaloisGroupUnramifiedOutside K Ω S → ℤ,
      (∀ x, ∀ u ∈ U, φ (x * u) = φ x) → (∀ z ∈ Z, ∀ x, φ (z * x) = φ x) →
      (Finset.univ.filter (fun q : GaloisGroupUnramifiedOutside K Ω S ⧸ U =>
        ∃ x : GaloisGroupUnramifiedOutside K Ω S, (x : GaloisGroupUnramifiedOutside K Ω S ⧸ U) = q ∧
          φ x ≠ 0)).card = n → IsCapitulating S ι ℓ (Pi.single v φ) from
    key _ φ hφU hφZ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφU hφZ hn
  by_cases h0 : ∀ x, φ x = 0
  · have : φ = 0 := funext h0
    rw [this, Pi.single_zero]
    exact isCapitulating_zero S ι ℓ
  simp only [not_forall] at h0
  obtain ⟨x₀, hx₀⟩ := h0
  set χ : GaloisGroupUnramifiedOutside K Ω S → ℤ := fun g => zuInd S ι v U (g * x₀⁻¹) with hχ
  have hmemD : ∀ g, (∃ z ∈ Z, ∃ u ∈ U, g * x₀⁻¹ = z * u) ↔ ∃ z ∈ Z, ∃ u ∈ U, g = z * x₀ * u := by
    intro g
    constructor
    · rintro ⟨z, hz, u, hu, h⟩
      refine ⟨z, hz, x₀⁻¹ * u * x₀, hUn.conj_mem' u hu x₀, ?_⟩
      calc g = g * x₀⁻¹ * x₀ := by group
        _ = _ := by rw [h]; group
    · rintro ⟨z, hz, u, hu, rfl⟩
      refine ⟨z, hz, x₀ * u * x₀⁻¹, hUn.conj_mem u hu x₀, by group⟩
  have hφD : ∀ z ∈ Z, ∀ u ∈ U, φ (z * x₀ * u) = φ x₀ := by
    intro z hz u hu
    rw [hφU _ u hu, hφZ z hz]
  set ψ : GaloisGroupUnramifiedOutside K Ω S → ℤ := fun g => φ g - φ x₀ * χ g with hψ
  have hχ1 : ∀ g, χ g = if ∃ z ∈ Z, ∃ u ∈ U, g = z * x₀ * u then 1 else 0 := by
    intro g
    simp only [hχ, zuInd, ← hZ, hmemD g]
  have hsplit : Pi.single v φ = Pi.single v ψ + (φ x₀) • fun v' x =>
      (Pi.single v (zuInd S ι v U) :
        {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
        v' (x * x₀⁻¹) := by
    funext v' x
    by_cases hv : v' = v
    · subst hv
      simp [hψ, hχ]
    · simp [Pi.single_eq_of_ne hv]
  rw [hsplit]
  refine IsCapitulating.add S ι ?_ ((hbase.translate S ι x₀⁻¹).zsmul S ι (φ x₀))
  refine ih _ ?_ ψ ?_ ?_ rfl
  · rw [← hn]
    apply Finset.card_lt_card
    refine ⟨fun q hq => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      obtain ⟨x, rfl, hx⟩ := hq
      refine ⟨x, rfl, fun hφx => hx ?_⟩
      have : χ x = 0 := by
        rw [hχ1]
        split_ifs with hD
        · obtain ⟨z, hz, u, hu, rfl⟩ := hD
          exact absurd (hφD z hz u hu ▸ hφx) hx₀
        · rfl
      simp [hψ, hφx, this]
    · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, x₀, rfl, hx₀⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      obtain ⟨x, hx, hψx⟩ := this
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, x = x₀ * u := by
        have h := QuotientGroup.eq.1 hx
        refine ⟨x₀⁻¹ * x, ?_, by group⟩
        have := U.inv_mem h
        rwa [mul_inv_rev, inv_inv] at this
      apply hψx
      have hD : ∃ z ∈ Z, ∃ u' ∈ U, x₀ * u = z * x₀ * u' := ⟨1, Z.one_mem, u, hu, by rw [one_mul]⟩
      simp only [hψ, hχ1, hD, ite_true, hφU x₀ u hu, mul_one, sub_self]
  · intro x u hu
    have hAB : (∃ z ∈ Z, ∃ u' ∈ U, x * u = z * x₀ * u') ↔ ∃ z ∈ Z, ∃ u' ∈ U, x = z * x₀ * u' := by
      constructor
      · rintro ⟨z, hz, u', hu', h⟩
        refine ⟨z, hz, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), ?_⟩
        rw [← mul_assoc, ← h, mul_inv_cancel_right]
      · rintro ⟨z, hz, u', hu', rfl⟩
        exact ⟨z, hz, u' * u, U.mul_mem hu' hu, mul_assoc _ _ _⟩
    simp only [hψ, hφU x u hu, hχ1, hAB]
  · intro z hz x
    have hAB : (∃ z' ∈ Z, ∃ u' ∈ U, z * x = z' * x₀ * u') ↔ ∃ z' ∈ Z, ∃ u' ∈ U, x = z' * x₀ * u' := by
      constructor
      · rintro ⟨z', hz', u', hu', h⟩
        refine ⟨z⁻¹ * z', Z.mul_mem (Z.inv_mem hz) hz', u', hu', ?_⟩
        simp only [mul_assoc] at h ⊢
        rw [← h, inv_mul_cancel_left]
      · rintro ⟨z', hz', u', hu', rfl⟩
        exact ⟨z * z', Z.mul_mem hz hz', u', hu', by simp only [mul_assoc]⟩
    simp only [hψ, hφZ z hz, hχ1, hAB]

omit [NumberField K] [IsGalois K Ω] in
open Classical in
theorem eq_sum_single (f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)
    (T : Finset {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (hT : ∀ v ∉ T, f v = 0) :
    f = ∑ v ∈ T, Pi.single v (f v) := by
  funext v
  rw [Finset.sum_apply, Finset.sum_pi_single]
  split_ifs with h
  · rfl
  · exact hT v h

variable {S} in
theorem sOrder_pow {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (y : (maximalUnramifiedOutside K Ω S)ˣ)
    (m : ℕ) : sOrder S ι v (y ^ m) = m * sOrder S ι v y := by
  induction m with
  | zero => simp [sOrder_one ι hv]
  | succ m ih => rw [pow_succ, sOrder_mul ι hv, ih]; push_cast; ring

omit [NumberField K] [IsGalois K Ω] in
theorem levelRestrict_eq_one_of_mem
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S))
    {u : GaloisGroupUnramifiedOutside K Ω S} (hu : u ∈ L.toIntermediateField.fixingSubgroup) :
    levelRestrict S L u = 1 := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  rw [levelRestrict_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hu z z.2

/-- An element of `G_S` lies in `Z_v · U_L` exactly when its restriction to `L` lies in the image of
the decomposition homomorphism of the embedding of `L` given by `ι`. -/
theorem mem_decompositionSubgroup_mul_iff (v : HeightOneSpectrum (𝓞 K))
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S))
    (g : GaloisGroupUnramifiedOutside K Ω S) :
    (∃ z ∈ decompositionSubgroup S ι v, ∃ u ∈ L.toIntermediateField.fixingSubgroup, g = z * u) ↔
      levelRestrict S L g ∈ (decompositionHom (v.adicCompletion K)
        (levelEmbedding S ι v L.toIntermediateField) :
          Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →* Gal(L/K)).range := by
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, u, hu, rfl⟩
    refine ⟨h, ?_⟩
    have hm : levelRestrict S L (localizationHom ι S v h * u) =
        levelRestrict S L (localizationHom ι S v h) * levelRestrict S L u := map_mul _ _ _
    erw [hm]
    rw [levelRestrict_eq_one_of_mem S L hu, mul_one]
    exact (levelRestrict_localizationHom S ι v L h).symm
  · rintro ⟨h, hh⟩
    refine ⟨localizationHom ι S v h, ⟨h, rfl⟩, (localizationHom ι S v h)⁻¹ * g, ?_, by group⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e := congrArg (fun τ : Gal(L/K) => ((τ ⟨x, hx⟩ : L) : maximalUnramifiedOutside K Ω S))
      (hh.symm.trans (levelRestrict_localizationHom S ι v L h).symm)
    simp only [levelRestrict_apply] at e
    rw [AlgEquiv.mul_apply, e, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

end Good

section Base

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsSepClosed Ω] (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

open Classical in
/-- The indicator of a single place of a finite Galois subextension is capitulating. -/
theorem isCapitulating_base {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S)) :
    IsCapitulating S ι ℓ (Pi.single v (zuInd S ι v L.toIntermediateField.fixingSubgroup)) := by
  have := NumberField.of_module_finite K L.toIntermediateField
  set j := levelEmbedding S ι v.1 L.toIntermediateField with hj
  set W := (placeOfAlgHom j).1 with hW
  obtain ⟨a, N, hN, hh⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (classNumber_ne_zero (K := L.toIntermediateField)) ℓ hℓ.one_lt.ne'
  set π : L.toIntermediateFieldˣ := placeUnit W with hπ
  have hval : ∀ w : HeightOneSpectrum (𝓞 L.toIntermediateField),
      w.valuation L.toIntermediateField (π : L.toIntermediateField) =
        if w = W then WithZero.exp (-(classNumber L.toIntermediateField : ℤ)) else 1 := by
    intro w
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, valuationOfNeZero_placeUnit]
    split_ifs <;> rfl
  -- transport to a subfield of `Ω`
  let L' : IntermediateField K Ω := L.toIntermediateField.map (maximalUnramifiedOutside K Ω S).val
  let φ : L.toIntermediateField ≃ₐ[K] L' :=
    IntermediateField.equivMap L.toIntermediateField (maximalUnramifiedOutside K Ω S).val
  have : FiniteDimensional K L' := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have : NumberField L' := NumberField.of_module_finite K L'
  have hL' : L' ≤ maximalUnramifiedOutside K Ω S := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let π' : L'ˣ := Units.map (φ : L.toIntermediateField →* L') π
  have hdiv : ∀ w' : HeightOneSpectrum (𝓞 L'), w'.under (𝓞 K) ∉ S →
      ((ℓ ^ a : ℕ) : ℤ) ∣ WithZero.log (w'.valuation L' (π' : L')) := by
    intro w' _
    have e := Langlands.Global.AdelicFunctoriality.finitePlaceEquiv_valuation φ.toRingEquiv w'
      (π : L.toIntermediateField)
    change _ = w'.valuation L' (π' : L') at e
    rw [← e, hval]
    split_ifs
    · rw [WithZero.log_exp, hh]
      exact ⟨-(N : ℤ), by push_cast; ring⟩
    · rw [WithZero.log_one]
      exact dvd_zero _
  have hnS : ∀ w ∉ S, (((ℓ ^ a : ℕ)) : 𝓞 K) ∉ w.asIdeal := by
    intro w hw hmem
    rw [Nat.cast_pow] at hmem
    exact hw (hS w (w.isPrime.mem_of_pow_mem _ hmem))
  have : NeZero (((ℓ ^ a : ℕ)) : Ω) := ⟨by
    rw [← map_natCast (algebraMap K Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 (pow_ne_zero a hℓ.ne_zero))⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq ((π' : L') : Ω) (ℓ ^ a)
  have hαS := mem_maximalUnramifiedOutside_of_pow_eq_of_dvd S hL' (pow_ne_zero a hℓ.ne_zero) hnS π'
    hdiv hα
  have hα0 : (⟨α, hαS⟩ : maximalUnramifiedOutside K Ω S) ≠ 0 := by
    intro h0
    have h' : α = 0 := congrArg Subtype.val h0
    rw [h', zero_pow (pow_ne_zero a hℓ.ne_zero)] at hα
    exact π'.ne_zero (Subtype.ext hα.symm)
  set y : (maximalUnramifiedOutside K Ω S)ˣ := Units.mk0 _ hα0
  set πS : (maximalUnramifiedOutside K Ω S)ˣ :=
    Units.map (L.toIntermediateField.val : L.toIntermediateField →* maximalUnramifiedOutside K Ω S) π
  have hπL : (πS : maximalUnramifiedOutside K Ω S) ∈ L.toIntermediateField := (π : L.toIntermediateField).2
  have hy : y ^ (ℓ ^ a) = πS := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
    exact hα))
  have hπunit : levelUnit πS hπL = π := Units.ext rfl
  -- the divisor function of `y`
  have key : ∀ (v' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (g : GaloisGroupUnramifiedOutside K Ω S),
      sOrder S ι v'.1 (galUnitsHom K _ g y) =
        N * (-(Pi.single v (zuInd S ι v L.toIntermediateField.fixingSubgroup) :
          {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ) v' g) := by
    intro v' g
    set τ := levelRestrict S L g
    set j' := levelEmbedding S ι v'.1 L.toIntermediateField
    have h1 : ((ℓ ^ a : ℕ) : ℤ) * sOrder S ι v'.1 (galUnitsHom K _ g y) =
        placeExponent v'.1 (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField)) π := by
      rw [← sOrder_pow ι v'.2, ← map_pow, hy, sOrder_galUnitsHom_eq ι v'.2 L hπL g, hπunit,
        placeExponent_comp_algEquiv]
      rfl
    have h2 : placeExponent v'.1 (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField)) π =
        if (placeOfAlgHom (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).1 = W
          then -(classNumber L.toIntermediateField : ℤ) else 0 := by
      apply WithZero.exp_injective
      rw [← valuation_eq_exp_placeExponent, hval]
      split_ifs <;> simp
    have h3 : (placeOfAlgHom (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).1 = W ↔
        v' = v ∧ ∃ z ∈ decompositionSubgroup S ι v.1,
          ∃ u ∈ L.toIntermediateField.fixingSubgroup, g = z * u := by
      constructor
      · intro hWW
        have hvv : v'.1 = v.1 := HeightOneSpectrum.ext ((placeOfAlgHom
          (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).2.over.trans
            ((congrArg (fun w : HeightOneSpectrum (𝓞 L.toIntermediateField) => w.asIdeal.under (𝓞 K))
              hWW).trans (placeOfAlgHom j).2.over.symm))
        have hvv' : v' = v := Subtype.ext hvv
        subst hvv'
        refine ⟨rfl, (mem_decompositionSubgroup_mul_iff S ι v'.1 L g).2 ?_⟩
        exact (placeOfAlgHom_comp_eq_iff v'.1 j τ).1 (Subtype.ext hWW)
      · rintro ⟨rfl, hz⟩
        exact congrArg Subtype.val ((placeOfAlgHom_comp_eq_iff v'.1 j τ).2
          ((mem_decompositionSubgroup_mul_iff S ι v'.1 L g).1 hz))
    have hpos : ((ℓ ^ a : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero a hℓ.ne_zero
    apply mul_left_cancel₀ hpos
    rw [h1, h2]
    by_cases hc : (placeOfAlgHom (j'.comp (τ : L.toIntermediateField →ₐ[K] L.toIntermediateField))).1 = W
    · obtain ⟨rfl, hz⟩ := h3.1 hc
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc), Pi.single_eq_same, zuInd,
        ite_eq_left_of_eq_true _ _ (eq_true hz), hh]
      push_cast
      ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      by_cases hvv : v' = v
      · subst hvv
        rw [Pi.single_eq_same, zuInd, ite_eq_right_of_eq_false _ _ (eq_false (fun hz => hc (h3.2 ⟨rfl, hz⟩)))]
        ring
      · rw [Pi.single_eq_of_ne hvv]
        simp
  have hneg : IsCapitulating S ι ℓ (-(Pi.single v (zuInd S ι v L.toIntermediateField.fixingSubgroup) :
      {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ)) :=
    ⟨N, Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hN), y, fun v' g => key v' g⟩
  have := hneg.zsmul S ι (-1)
  simpa using this

omit [IsSepClosed Ω] in
/-- A locally constant function on `G_S` is right invariant under the fixing subgroup of some finite
Galois subextension of `K_S`. -/
theorem exists_level_mul_eq (φ : GaloisGroupUnramifiedOutside K Ω S → ℤ) (hφ : IsLocallyConstant φ) :
    ∃ L : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S),
      ∀ x, ∀ u ∈ L.toIntermediateField.fixingSubgroup, φ (x * u) = φ x := by
  obtain ⟨V, hV, hVφ⟩ := exists_mem_nhds_one_forall_mul_eq hφ
  obtain ⟨E, hEf, hEV⟩ := (krullTopology_mem_nhds_one_iff K (maximalUnramifiedOutside K Ω S) V).1 hV
  obtain ⟨L, hEL⟩ := exists_finiteGaloisIntermediateField_le E
  refine ⟨L, fun x u hu => hVφ x u (hEV ?_)⟩
  exact IntermediateField.fixingSubgroup_le hEL hu

open Classical in
/-- Every left `Z_v`-invariant locally constant function at a place `v ∉ S` is capitulating. -/
theorem isCapitulating_single {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (φ : GaloisGroupUnramifiedOutside K Ω S → ℤ)
    (hφ : IsLocallyConstant φ)
    (hZ : ∀ σ x, φ (localizationHom ι S v.1 σ * x) = φ x) :
    IsCapitulating S ι ℓ (Pi.single v φ) := by
  obtain ⟨L, hL⟩ := exists_level_mul_eq S φ hφ
  have : (L.toIntermediateField.fixingSubgroup).Normal := inferInstance
  refine isCapitulating_single_of_base S ι v L.toIntermediateField.fixingSubgroup
    (IntermediateField.fixingSubgroup_isOpen L.toIntermediateField)
    (isCapitulating_base S ι hℓ hS v L) φ hL ?_
  rintro _ ⟨σ, rfl⟩ x
  exact hZ σ x

/-- **Capitulation.** If `S` contains the places above the prime `ℓ`, for every divisor `f` of
`K_S` prime to `S` some multiple `N f` with `ℓ ∤ N` is the divisor of a unit of `K_S`. -/
theorem exists_coprime_nsmul_eq_unitsToSDivisor {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (f : sDivisorModule S ι) :
    ∃ N : ℕ, N.Coprime ℓ ∧ ∃ y : (maximalUnramifiedOutside K Ω S)ˣ,
      (unitsToSDivisor S ι).hom (Additive.ofMul y) = N • f := by
  classical
  let f' : divisorFunctions (outsideLocalizationHom S ι) (ULift.{u} ℤ) := f
  let F : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → GaloisGroupUnramifiedOutside K Ω S → ℤ :=
    fun v g => (f'.1 v g).down
  have hf := f'.2
  have hF : IsCapitulating S ι ℓ F := by
    rw [eq_sum_single S F hf.1.toFinset (fun v hv => by
      have : f'.1 v = 0 := by simpa using hv
      funext g
      change (f'.1 v g).down = 0
      rw [this]
      rfl)]
    refine isCapitulating_sum S ι _ _ fun v _ => ?_
    refine isCapitulating_single S ι hℓ hS v _ ((hf.2 v).1.comp ULift.down) fun σ x => ?_
    change (f'.1 v (localizationHom ι S v.1 σ * x)).down = _
    rw [(hf.2 v).2 σ x]
  obtain ⟨N, hN, y, hy⟩ := hF
  refine ⟨N, hN, y, Subtype.ext ?_⟩
  funext v g
  apply ULift.ext
  change sOrder S ι v.1 (galUnitsHom K _ g y) = N • F v g
  rw [hy v g, nsmul_eq_mul]

end Base

end

end Langlands.GaloisCohomology
