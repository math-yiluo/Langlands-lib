import Langlands.Representation.Archimedean.ComplexPermutationKMap
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Langlands.Representation.Archimedean.ComplexJacquetFrobenius

/-!
# Permutation invariance for one adjacent swap

Let `ds = pre ++ d :: e :: post` and `es = pre ++ e :: d :: post`, and suppose the
`U(n)`-finite functions `X(ds)` of the standard module of `ds` form an irreducible
`(𝔤𝔩_n(ℂ), U(n))`-module. This file produces a bijective intertwining map `X(es) → X(ds)`
(`exists_bijective_swap`), from

* a nonzero Jacquet functional on `X(ds)` with the exponents of `es`, or on `X(es)` with the
  exponents of `ds` (`SwapJacquetStatement`, supplied by the rank-one intertwining integral);
* Frobenius reciprocity (`ComplexJacquetFrobeniusStatement`), which turns it into a nonzero
  intertwining map `X(ds) → X(es)` or `X(es) → X(ds)`;
* irreducibility of `X(ds)`, which makes the first map injective and the second surjective;
* the `U(n)`-equivariant injections of `ComplexPermutationKMap` and the upgrade lemmas of
  `ComplexPermutationKType`, which make an injective map `X(ds) → X(es)` surjective and a
  surjective map `X(es) → X(ds)` injective.

If `d` and `e` have the same weight and exponent, then `d = e`, `es = ds`, and the identity
works.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexPermutation

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

/-! ## Lists -/

theorem length_swap (pre post : List ComplexCharacterData) (d e : ComplexCharacterData) :
    (pre ++ e :: d :: post).length = (pre ++ d :: e :: post).length := by
  simp

/-- The exponents `2 t_j + (n - 1) - 2 j` of the characters of a list of length `n`. -/
def listExponent (n : ℕ) (es : List ComplexCharacterData) (hes : es.length = n) (j : Fin n) :
    ℂ :=
  2 * (es.get (Fin.cast hes.symm j)).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)

/-- The imaginary exponents `i l_j` of the characters of a list of length `n`. -/
def listWeight (n : ℕ) (es : List ComplexCharacterData) (hes : es.length = n) (j : Fin n) :
    ℂ :=
  Complex.I * ((es.get (Fin.cast hes.symm j)).weight : ℂ)

/-- **Rank-one Jacquet functionals** (supplied by the rank-one intertwining integral): for
`ds = pre ++ d :: e :: post` with `Re t_d ≥ Re t_e` and `(l_d, t_d) ≠ (l_e, t_e)`, the
`U(n)`-finite functions of the standard module of `ds` have a nonzero Jacquet functional whose
exponents are those of `es = pre ++ e :: d :: post`. -/
def SwapJacquetStatement : Prop :=
  ∀ (pre post : List ComplexCharacterData) (d e : ComplexCharacterData) (n : ℕ)
    (hn : (pre ++ d :: e :: post).length = n),
    0 ≤ (d.exponent - e.exponent).re → (d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent) →
      ∃ ℓ : (KF n (pre ++ d :: e :: post)) →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        IsComplexJacquetFunctional n (complexStandardLie n (pre ++ d :: e :: post)) ℓ
          (listExponent n (pre ++ e :: d :: post) ((length_swap pre post d e).trans hn))
          (listWeight n (pre ++ e :: d :: post) ((length_swap pre post d e).trans hn))

/-- The character at each position, read off the list. -/
theorem complexPositionCharacter_eq_get :
    ∀ (l : List ComplexCharacterData) (p : ℕ) (hp : p < l.length),
      complexPositionCharacter l p = fun z => ((l.get ⟨p, hp⟩).character z : ℂ)
  | [], p, hp => absurd hp (Nat.not_lt_zero p)
  | _ :: _, 0, _ => rfl
  | _ :: l, p + 1, hp => complexPositionCharacter_eq_get l p (Nat.lt_of_succ_lt_succ hp)

theorem complexPositionCharacter_of_length_le :
    ∀ (l : List ComplexCharacterData) (p : ℕ), l.length ≤ p →
      complexPositionCharacter l p = fun _ => 1
  | [], _, _ => by cases ‹ℕ› <;> rfl
  | _ :: _, 0, hp => absurd hp (by simp)
  | _ :: l, p + 1, hp =>
    complexPositionCharacter_of_length_le l p (Nat.le_of_succ_le_succ (by simpa using hp))

/-- Two lists of the same length with the same characters at every position have the same
position characters. -/
theorem complexPositionCharacter_congr {l₁ l₂ : List ComplexCharacterData}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (p : ℕ) (h₁ : p < l₁.length) (h₂ : p < l₂.length),
      (l₁.get ⟨p, h₁⟩).character = (l₂.get ⟨p, h₂⟩).character) :
    complexPositionCharacter l₁ = complexPositionCharacter l₂ := by
  funext p
  by_cases hp : p < l₁.length
  · rw [complexPositionCharacter_eq_get l₁ p hp,
      complexPositionCharacter_eq_get l₂ p (hlen ▸ hp), h p hp (hlen ▸ hp)]
  · push Not at hp
    rw [complexPositionCharacter_of_length_le l₁ p hp,
      complexPositionCharacter_of_length_le l₂ p (hlen ▸ hp)]

/-- Weight and exponent determine the character. -/
theorem character_eq_of_params {d e : ComplexCharacterData} (hw : d.weight = e.weight)
    (ht : d.exponent = e.exponent) : d.character = e.character := by
  ext z
  rw [d.character_eq, e.character_eq, hw, ht]

/-- Weight and exponent determine the character data. -/
theorem eq_of_params {d e : ComplexCharacterData} (hw : d.weight = e.weight)
    (ht : d.exponent = e.exponent) : d = e := by
  have hc := character_eq_of_params hw ht
  cases d
  cases e
  simp_all

/-! ## Transport along equal position characters -/

theorem kf_eq_of_complexPositionCharacter_eq {n : ℕ} {l₁ l₂ : List ComplexCharacterData}
    (h : complexPositionCharacter l₁ = complexPositionCharacter l₂) : KF n l₁ = KF n l₂ := by
  simp only [KF, complexStandardModule, h]

/-- The identity on functions, between the `U(n)`-finite functions of two lists with the same
position characters. -/
def kfEquiv {n : ℕ} {l₁ l₂ : List ComplexCharacterData}
    (h : complexPositionCharacter l₁ = complexPositionCharacter l₂) :
    (KF n l₁) ≃ₗ[ℂ] (KF n l₂) :=
  LinearEquiv.ofEq _ _ (kf_eq_of_complexPositionCharacter_eq h)

@[simp]
theorem kfEquiv_coe {n : ℕ} {l₁ l₂ : List ComplexCharacterData}
    (h : complexPositionCharacter l₁ = complexPositionCharacter l₂) (f : KF n l₁) :
    ((kfEquiv h f : KF n l₂) : Langlands.GeneralLinear n ℂ → ℂ) = f :=
  rfl

/-! ## Embeddings and intertwining maps -/

/-- An embedding `S : X(ds) → X(es)` (for the action on `X(ds)`) is an intertwining map from
`X(ds)` into the module `X(es)`. -/
theorem intertwining_of_embedding {n : ℕ} {ds es : List ComplexCharacterData}
    {S : (KF n ds) →ₗ[ℂ] (KF n es)}
    (hS : IsComplexStandardEmbedding n (complexStandardRep n ds) (complexStandardLie n ds) es S) :
    IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds S := by
  refine ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 k.2,
    ?_⟩, fun X f => ⟨rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X, ?_⟩⟩
  · apply Subtype.ext
    have h := hS.1 k f
    have hk : (⟨_, rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 k.2⟩ :
        KF n ds) = complexStandardRep n ds
          ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ f := by
      apply Subtype.ext
      rw [principalSeriesRep_apply_coe]
      exact congrArg (fun g => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) g
        (f : Langlands.GeneralLinear n ℂ → ℂ)) (toUnits_toUnitary k).symm
    rw [hk, h, principalSeriesRep_apply_coe]
    exact congrArg (fun g => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) g
      ((S f : KF n es) : Langlands.GeneralLinear n ℂ → ℂ)) (toUnits_toUnitary k).symm
  · apply Subtype.ext
    have h := hS.2 X f
    have hX : (⟨_, rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X⟩ :
        KF n ds) = complexStandardLie n ds (1 ⊗ₜ X) f := by
      apply Subtype.ext
      rw [principalSeriesLie_one_tmul_apply_coe]
    rw [hX, h, principalSeriesLie_one_tmul_apply_coe]

/-- `U(n)`-equivariance of an intertwining map between standard modules, in the form used by
the upgrade lemmas. -/
theorem equivariant_of_intertwining {n : ℕ} {ds es : List ComplexCharacterData}
    {S : (KF n es) →ₗ[ℂ] (KF n ds)}
    (hS : IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds)
      es S) (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es) :
    S (complexStandardRep n es k f) = complexStandardRep n ds k (S f) :=
  hS.map_rep k f

/-- The inverse of a bijective embedding `X(ds) → X(es)` is an intertwining map
`X(es) → X(ds)`. -/
theorem intertwining_symm_of_embedding {n : ℕ} {ds es : List ComplexCharacterData}
    {S : (KF n ds) →ₗ[ℂ] (KF n es)} (hSbij : Function.Bijective S)
    (hS : IsComplexStandardEmbedding n (complexStandardRep n ds) (complexStandardLie n ds) es S) :
    IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) es
      ((LinearEquiv.ofBijective S hSbij).symm : (KF n es) →ₗ[ℂ] (KF n ds)) := by
  refine ⟨fun k h => ⟨rightTranslation_mem_kFiniteFunctions_complexStandardModule n es h.2 k.2,
    ?_⟩, fun X h => ⟨rightDerivative_mem_kFiniteFunctions_complexStandardModule n es h.2 X, ?_⟩⟩
  · obtain ⟨f, rfl⟩ := hSbij.2 h
    change (LinearEquiv.ofBijective S hSbij).symm _ =
      complexStandardRep n ds _ ((LinearEquiv.ofBijective S hSbij).symm (S f))
    rw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearEquiv.ofBijective_apply, hS.1 k f]
  · obtain ⟨f, rfl⟩ := hSbij.2 h
    change (LinearEquiv.ofBijective S hSbij).symm _ =
      complexStandardLie n ds _ ((LinearEquiv.ofBijective S hSbij).symm (S f))
    rw [LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearEquiv.ofBijective_apply, hS.2 X f]

/-! ## The `U(n)`-equivariant injections for a swap -/

theorem ofFn_get_eq {n : ℕ} (l : List ComplexCharacterData) (hl : l.length = n) :
    List.ofFn (fun j : Fin n => l.get (Fin.cast hl.symm j)) = l := by
  subst hl
  exact List.ofFn_get l

/-- The swap of the positions `pre.length` and `pre.length + 1`. -/
def swapPerm {n : ℕ} (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
    (hn : (pre ++ d :: e :: post).length = n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨pre.length, by rw [← hn]; simp⟩ ⟨pre.length + 1, by rw [← hn]; simp⟩

theorem get_swap {n : ℕ} (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
    (hn : (pre ++ d :: e :: post).length = n) (k : Fin n) :
    (pre ++ d :: e :: post).get (Fin.cast hn.symm ((swapPerm pre post d e hn).symm k)) =
      (pre ++ e :: d :: post).get (Fin.cast ((length_swap pre post d e).trans hn).symm k) := by
  obtain ⟨k, hk⟩ := k
  simp only [swapPerm, Equiv.symm_swap, List.get_eq_getElem, Fin.val_cast]
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [Fin.ext_iff] at h1
    simp only at h1
    subst h1
    simp
  · rw [Fin.ext_iff] at h2
    simp only at h2
    subst h2
    simp
  · rw [Fin.ext_iff] at h1 h2
    simp only at h1 h2 ⊢
    rcases lt_or_ge k pre.length with h | h
    · rw [List.getElem_append_left h, List.getElem_append_left h]
    · rw [List.getElem_append_right h, List.getElem_append_right h]
      obtain ⟨m, hm⟩ : ∃ m, k - pre.length = m + 2 := ⟨k - pre.length - 2, by omega⟩
      simp only [hm, List.getElem_cons_succ]

/-- An injective `U(n)`-equivariant map `X(pre ++ d :: e :: post) → X(pre ++ e :: d :: post)`. -/
theorem exists_kMap_swap {n : ℕ} (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hn : (pre ++ d :: e :: post).length = n) :
    ∃ Φ : (KF n (pre ++ d :: e :: post)) →ₗ[ℂ] (KF n (pre ++ e :: d :: post)),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (pre ++ d :: e :: post)),
        Φ (complexStandardRep n (pre ++ d :: e :: post) k f) =
          complexStandardRep n (pre ++ e :: d :: post) k (Φ f)) ∧ Function.Injective Φ := by
  set dd : Fin n → ComplexCharacterData :=
    fun j => (pre ++ d :: e :: post).get (Fin.cast hn.symm j) with hdd
  set σ := swapPerm pre post d e hn with hσ
  have h1 : List.ofFn dd = pre ++ d :: e :: post := ofFn_get_eq _ hn
  have h2 : List.ofFn (fun k => dd (σ.symm k)) = pre ++ e :: d :: post := by
    rw [← ofFn_get_eq (pre ++ e :: d :: post) ((length_swap pre post d e).trans hn)]
    congr 1
    funext k
    exact get_swap pre post d e hn k
  have h := (⟨permKMap dd σ, permKMap_equivariant dd σ, permKMap_injective dd σ⟩ :
    ∃ Φ : (KF n (List.ofFn dd)) →ₗ[ℂ] (KF n (List.ofFn fun k => dd (σ.symm k))),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (List.ofFn dd)),
        Φ (complexStandardRep n (List.ofFn dd) k f) =
          complexStandardRep n (List.ofFn fun k => dd (σ.symm k)) k (Φ f)) ∧
        Function.Injective Φ)
  rw [h1, h2] at h
  exact h

/-! ## From a Jacquet functional to an embedding -/

/-- Frobenius reciprocity applied to a nonzero Jacquet functional on `X(ds)` with the exponents
of a list `es` of length `n` gives a nonzero embedding `X(ds) → X(es)`. -/
theorem exists_embedding_of_jacquet (hFR : ComplexJacquetFrobeniusStatement.{0}) {n : ℕ}
    (ds es : List ComplexCharacterData) (hes : es.length = n) (ℓ : (KF n ds) →ₗ[ℂ] ℂ)
    (hℓ : ℓ ≠ 0)
    (hJ : IsComplexJacquetFunctional n (complexStandardLie n ds) ℓ (listExponent n es hes)
      (listWeight n es hes)) :
    ∃ S : (KF n ds) →ₗ[ℂ] (KF n es), S ≠ 0 ∧
      IsComplexStandardEmbedding n (complexStandardRep n ds) (complexStandardLie n ds) es S := by
  obtain ⟨dd, hda, hdb, B, hB0, hB⟩ := hFR n (KF n ds) (complexStandardRep n ds)
    (complexStandardLie n ds) (isComplexGKModule_complexStandardModule n ds) ℓ _ _ hℓ hJ
  -- the characters of `dd` are those of `es`
  have hparams : ∀ j : Fin n, dd j = es.get (Fin.cast hes.symm j) := by
    intro j
    apply eq_of_params
    · have h := hdb j
      rw [listWeight] at h
      have h' : ((dd j).weight : ℂ) = ((es.get (Fin.cast hes.symm j)).weight : ℂ) :=
        mul_left_cancel₀ Complex.I_ne_zero h
      exact_mod_cast h'
    · have h := hda j
      rw [listExponent] at h
      have h' : 2 * (dd j).exponent = 2 * (es.get (Fin.cast hes.symm j)).exponent := by
        linear_combination h
      exact mul_left_cancel₀ two_ne_zero h'
  have hlist : List.ofFn dd = es := by
    rw [← ofFn_get_eq es hes]
    congr 1
    funext j
    exact hparams j
  subst hlist
  exact ⟨B, hB0, hB⟩

/-! ## The swap -/

/-- **One adjacent swap.** If `X(pre ++ d :: e :: post)` is irreducible, there is a bijective
intertwining map from `X(pre ++ e :: d :: post)` onto it. -/
theorem exists_bijective_swap (hJ : SwapJacquetStatement)
    (hFR : ComplexJacquetFrobeniusStatement.{0}) {n : ℕ} (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hn : (pre ++ d :: e :: post).length = n)
    (hirr : IsIrreducibleGKModule (complexStandardRep n (pre ++ d :: e :: post))
      (complexStandardLie n (pre ++ d :: e :: post))) :
    ∃ T : (KF n (pre ++ e :: d :: post)) →ₗ[ℂ] (KF n (pre ++ d :: e :: post)),
      Function.Bijective T ∧
        IsComplexStandardIntertwining n (complexStandardRep n (pre ++ d :: e :: post))
          (complexStandardLie n (pre ++ d :: e :: post)) (pre ++ e :: d :: post) T := by
  set ds := pre ++ d :: e :: post with hds
  set es := pre ++ e :: d :: post with hes
  have hn' : es.length = n := (length_swap pre post d e).trans hn
  -- equal parameters: `d = e`
  by_cases hde : d.weight = e.weight ∧ d.exponent = e.exponent
  · have hdeq := eq_of_params hde.1 hde.2
    have hdses : es = ds := by rw [hes, hds, hdeq]
    rw [hdses]
    exact ⟨LinearMap.id, Function.bijective_id, isComplexStandardIntertwining_id n ds⟩
  have hne : d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent := by tauto
  obtain ⟨Φ₁, hΦ₁, hΦ₁inj⟩ := exists_kMap_swap pre post d e hn
  obtain ⟨Φ₂, hΦ₂, hΦ₂inj⟩ := exists_kMap_swap pre post e d hn'
  rcases le_total 0 (d.exponent - e.exponent).re with hre | hre
  · -- a nonzero embedding `X(ds) → X(es)`: injective, hence bijective
    obtain ⟨ℓ, hℓ, hJℓ⟩ := hJ pre post d e n hn hre hne
    obtain ⟨S, hS0, hS⟩ := exists_embedding_of_jacquet hFR ds es hn' ℓ hℓ hJℓ
    have hSint := intertwining_of_embedding hS
    have hSinj : Function.Injective S := injective_of_isIrreducibleGKModule hirr hSint hS0
    have hSsurj : Function.Surjective S :=
      surjective_of_injective_of_kMap ds es S (equivariant_of_intertwining hSint) hSinj Φ₂
        hΦ₂ hΦ₂inj
    exact ⟨_, (LinearEquiv.ofBijective S ⟨hSinj, hSsurj⟩).symm.bijective,
      intertwining_symm_of_embedding ⟨hSinj, hSsurj⟩ hS⟩
  · -- a nonzero embedding `X(es) → X(ds)`: surjective, hence bijective
    have hre' : 0 ≤ (e.exponent - d.exponent).re := by
      rw [← neg_sub, Complex.neg_re]
      linarith
    have hne' : e.weight ≠ d.weight ∨ e.exponent ≠ d.exponent := by
      rcases hne with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)
    obtain ⟨ℓ, hℓ, hJℓ⟩ := hJ pre post e d n hn' hre' hne'
    obtain ⟨S, hS0, hS⟩ := exists_embedding_of_jacquet hFR es ds hn ℓ hℓ hJℓ
    have hSint := intertwining_of_embedding hS
    -- the range is a nonzero invariant subspace of the irreducible `X(ds)`
    have hrange : LinearMap.range S = ⊥ ∨ LinearMap.range S = ⊤ := by
      apply hirr.2
      · rintro k _ ⟨f, rfl⟩
        exact ⟨_, hSint.map_rep k f⟩
      · rintro Y _ ⟨f, rfl⟩
        exact ⟨_, hSint.map_lie Y f⟩
    have hSsurj : Function.Surjective S := by
      rcases hrange with h | h
      · exact absurd (LinearMap.range_eq_bot.mp h) hS0
      · exact LinearMap.range_eq_top.mp h
    have hSinj : Function.Injective S :=
      injective_of_surjective_of_kMaps ds es S (equivariant_of_intertwining hSint) hSsurj
        Φ₁ hΦ₁ hΦ₁inj Φ₂ hΦ₂ hΦ₂inj
    exact ⟨S, ⟨hSinj, hSsurj⟩, hSint⟩

end Langlands.Archimedean.ComplexPermutation
