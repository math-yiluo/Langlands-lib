import Langlands.Representation.Archimedean.ComplexBlockRestriction
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwap

/-!
# Swapping adjacent unlinked characters, from the case `GL_2(ℂ)`

`ComplexStandardUnlinkedSwapReductionStatement`: the irreducibility of unlinked standard modules
of `GL_2(ℂ)` (`ComplexGLTwoUnlinkedIrreducibleStatement`) implies
`ComplexStandardUnlinkedSwapStatement`. The theorem `complexStandardUnlinkedSwapReduction`
proves it. See the Markdown file for the argument.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexBlock

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-! ## Frobenius reciprocity with the value at the identity -/

/-- Frobenius reciprocity for Jacquet functionals (as in `complexJacquetFrobenius`), keeping the
value at the identity: the Frobenius map `B` satisfies `(B w)(1) = ℓ(w)`. -/
theorem exists_frobenius_eval_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hgk : IsComplexGKModule n ρ π) (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n → ℂ) (hℓ : ℓ ≠ 0)
    (hJ : IsComplexJacquetFunctional n π ℓ a b) :
    ∃ dd : Fin n → ComplexCharacterData,
      (∀ j : Fin n, 2 * (dd j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) = a j) ∧
      (∀ j : Fin n, Complex.I * ((dd j).weight : ℂ) = b j) ∧
      ∃ B : V →ₗ[ℂ] KFs n (List.ofFn dd),
        (∀ w, (B w : Langlands.GeneralLinear n ℂ → ℂ) 1 = ℓ w) ∧
          IsComplexStandardEmbedding n ρ π (List.ofFn dd) B := by
  obtain ⟨l, hl, hT⟩ := hJ.exists_weight hgk hℓ
  set dd : Fin n → ComplexCharacterData := fun j =>
    characterOfParams (l j) ((a j - ((n : ℂ) - 1) + 2 * ((j : ℕ) : ℂ)) / 2) with hdd
  have hda : ∀ j : Fin n, 2 * (dd j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) = a j := by
    intro j
    simp only [hdd, characterOfParams_exponent]
    ring
  have hdl : ∀ j : Fin n, (dd j).weight = l j := fun j => by simp [hdd]
  refine ⟨dd, hda, fun j => by rw [hdl, hl j], ?_⟩
  have hmem : ∀ w : V, frobeniusFunction ρ ℓ l a w ∈ KFs n (List.ofFn dd) := by
    intro w
    refine ⟨⟨contMDiff_frobeniusFunction hgk hT a w, fun a' u g => ?_⟩,
      frobeniusFunction_mem_kFiniteVectors hT a w (hgk.1 w)⟩
    rw [frobeniusFunction_diagonal_mul hT a w a' u g, principalSeriesCharacter_ofFn]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [hdl, hda]
  let B : V →ₗ[ℂ] KFs n (List.ofFn dd) :=
    { toFun := fun w => ⟨frobeniusFunction ρ ℓ l a w, hmem w⟩
      map_add' := fun w w' => Subtype.ext (frobeniusFunction_add a w w')
      map_smul' := fun c w => Subtype.ext (frobeniusFunction_smul a c w) }
  have hB : ∀ w, (B w : Langlands.GeneralLinear n ℂ → ℂ) = frobeniusFunction ρ ℓ l a w :=
    fun _ => rfl
  refine ⟨B, fun w => ?_, ⟨fun k v => ?_, fun X v => ?_⟩⟩
  · rw [hB]
    have h2 := frobeniusFunction_eq hT a w 1 1 Matrix.blockTriangular_one isUnit_one (by simp)
    rw [borelChar_one, one_mul, map_one, Module.End.one_apply] at h2
    exact h2
  · rw [hB, hB]
    funext g
    exact (frobeniusFunction_mul_unitary hT a v g k _ rfl).symm
  · rw [hB, hB]
    funext g
    exact (rightDerivative_frobeniusFunction hgk hJ hT v X g).symm

/-- Frobenius reciprocity applied to a nonzero Jacquet functional `ℓ` on `X(ds)` with the
exponents of a list `es`: an embedding `S : X(ds) → X(es)` with `(S f)(1) = ℓ(f)` (as in
`ComplexPermutation.exists_embedding_of_jacquet`). -/
theorem exists_embedding_eval_one (ds es : List ComplexCharacterData) (hes : es.length = n)
    (ℓ : KFs n ds →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    (hJ : IsComplexJacquetFunctional n (complexStandardLie n ds) ℓ
      (ComplexPermutation.listExponent n es hes) (ComplexPermutation.listWeight n es hes)) :
    ∃ S : KFs n ds →ₗ[ℂ] KFs n es,
      (∀ f, (S f : Langlands.GeneralLinear n ℂ → ℂ) 1 = ℓ f) ∧
        IsComplexStandardEmbedding n (complexStandardRep n ds) (complexStandardLie n ds) es S := by
  obtain ⟨dd, hda, hdb, B, hB1, hB⟩ := exists_frobenius_eval_one (complexStandardRep n ds)
    (complexStandardLie n ds) (isComplexGKModule_complexStandardModule n ds) ℓ _ _ hℓ hJ
  have hparams : ∀ j : Fin n, dd j = es.get (Fin.cast hes.symm j) := by
    intro j
    apply ComplexPermutation.eq_of_params
    · have h := hdb j
      rw [ComplexPermutation.listWeight] at h
      have h' : ((dd j).weight : ℂ) = ((es.get (Fin.cast hes.symm j)).weight : ℂ) :=
        mul_left_cancel₀ Complex.I_ne_zero h
      exact_mod_cast h'
    · have h := hda j
      rw [ComplexPermutation.listExponent] at h
      have h' : 2 * (dd j).exponent = 2 * (es.get (Fin.cast hes.symm j)).exponent := by
        linear_combination h
      exact mul_left_cancel₀ two_ne_zero h'
  have hlist : List.ofFn dd = es := by
    rw [← ComplexPermutation.ofFn_get_eq es hes]
    congr 1
    funext j
    exact hparams j
  subst hlist
  exact ⟨B, hB1, hB⟩

/-! ## The swap embedding is bijective -/

variable (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)

/-- **Main lemma.** If `Re t_d ≥ Re t_e`, `(l_d, t_d) ≠ (l_e, t_e)` and `d`, `e` are not linked,
then there is a bijective embedding `X(pre ++ d :: e :: post) → X(pre ++ e :: d :: post)`. -/
theorem exists_bijective_embedding (hirr : ComplexGLTwoUnlinkedIrreducibleStatement)
    (hn : (pre ++ d :: e :: post).length = n) (hre : 0 ≤ (d.exponent - e.exponent).re)
    (hne : d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent) (hlink : ¬ IsComplexLinked d e) :
    ∃ S : KFs n (pre ++ d :: e :: post) →ₗ[ℂ] KFs n (pre ++ e :: d :: post),
      Function.Bijective S ∧
        IsComplexStandardEmbedding n (complexStandardRep n (pre ++ d :: e :: post))
          (complexStandardLie n (pre ++ d :: e :: post)) (pre ++ e :: d :: post) S := by
  have hn' : (pre ++ e :: d :: post).length = n :=
    (ComplexPermutation.length_swap pre post d e).trans hn
  have hp : pre.length + 2 ≤ n := by
    rw [← hn, List.length_append, List.length_cons, List.length_cons]
    omega
  obtain ⟨c, hc⟩ := exists_lamTwo_ne_zero d e (shift n pre.length) hre hne
  have hkey := eq_bot_of_lamN pre.length hp pre post d e rfl hirr hn hre hlink c hc
  -- `Λ_c^{(n)} ≠ 0`: otherwise the whole module would vanish
  have hℓ : lamN pre.length hp pre post d e rfl hn hre c ≠ 0 := by
    intro h0
    have htop := hkey ⊤ (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
      (fun w _ => by rw [h0, LinearMap.zero_apply])
    obtain ⟨c', f, hf, hint⟩ := ComplexSwapJacquet.exists_integral_integrand_ne_zero pre post d e
      n hn (pos pre.length hp 0) (pos pre.length hp 1) (hi_pos pre.length hp pre rfl) (hj_pos pre.length hp) hre hne
    apply hint
    have hf0 : (⟨f, hf⟩ : KFs n (pre ++ d :: e :: post)) = 0 := by
      have hmem : (⟨f, hf⟩ : KFs n (pre ++ d :: e :: post)) ∈
          (⊤ : Submodule ℂ (KFs n (pre ++ d :: e :: post))) := Submodule.mem_top
      rw [htop] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    rw [← ComplexSwapJacquet.functional_apply
      (ComplexSwapJacquet.chartLieFacts _ hn (pos pre.length hp 0) (pos pre.length hp 1) (hj_pos pre.length hp))
      (ComplexSwapJacquet.chartDecay pre post d e (pos pre.length hp 0) (pos pre.length hp 1)
        (hi_pos pre.length hp pre rfl) (hj_pos pre.length hp) hre) c' ⟨f, hf⟩, hf0, map_zero]
  obtain ⟨S, hS1, hS⟩ := exists_embedding_eval_one _ _ hn' _ hℓ
    (isJacquet_lamN pre.length hp pre post d e rfl hn hn' hre c)
  have hSint := ComplexPermutation.intertwining_of_embedding hS
  -- the kernel is stable and killed by `Λ_c^{(n)}`
  have hSinj : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot]
    apply hkey
    · intro k w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hSint.map_rep k w, hw, map_zero]
    · intro X w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hSint.map_lie X w, hw, map_zero]
    · intro w hw
      rw [← hS1 w, LinearMap.mem_ker.mp hw]
      rfl
  obtain ⟨Φ₂, hΦ₂, hΦ₂inj⟩ := ComplexPermutation.exists_kMap_swap pre post e d hn'
  have hSsurj := ComplexPermutation.surjective_of_injective_of_kMap _ _ S
    (ComplexPermutation.equivariant_of_intertwining hSint) hSinj Φ₂ hΦ₂ hΦ₂inj
  exact ⟨S, ⟨hSinj, hSsurj⟩, hS⟩

end Langlands.Archimedean.ComplexBlock

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean ComplexBlock

/-- **Reduction to `GL_2(ℂ)`**: the irreducibility of the standard modules of two unlinked
characters of `GL_2(ℂ)` implies that adjacent unlinked characters of a standard module of
`GL_n(ℂ)` can be swapped. -/
def ComplexStandardUnlinkedSwapReductionStatement : Prop :=
  ComplexGLTwoUnlinkedIrreducibleStatement → ComplexStandardUnlinkedSwapStatement

/-- Proof of the reduction: for `Re t_d ≥ Re t_e` the swap embedding of
`ComplexBlock.exists_bijective_embedding` is inverted, for `Re t_d ≤ Re t_e` the swap
embedding of `(e, d)` is used directly, and for equal parameters `d = e`. -/
theorem complexStandardUnlinkedSwapReduction : ComplexStandardUnlinkedSwapReductionStatement := by
  intro hirr n pre post d e hn hlink
  by_cases hde : d.weight = e.weight ∧ d.exponent = e.exponent
  · have hdeq := ComplexPermutation.eq_of_params hde.1 hde.2
    subst hdeq
    exact ⟨LinearMap.id, Function.bijective_id, isComplexStandardIntertwining_id n _⟩
  have hne : d.weight ≠ e.weight ∨ d.exponent ≠ e.exponent := by tauto
  have hn' : (pre ++ e :: d :: post).length = n :=
    (ComplexPermutation.length_swap pre post d e).trans hn
  have hp : pre.length + 2 ≤ n := by
    rw [← hn, List.length_append, List.length_cons, List.length_cons]
    omega
  rcases le_total 0 (d.exponent - e.exponent).re with hre | hre
  · obtain ⟨S, hSbij, hS⟩ :=
      exists_bijective_embedding pre post d e hirr hn hre hne hlink
    exact ⟨_, (LinearEquiv.ofBijective S hSbij).symm.bijective,
      ComplexPermutation.intertwining_symm_of_embedding hSbij hS⟩
  · have hre' : 0 ≤ (e.exponent - d.exponent).re := by
      rw [← neg_sub, Complex.neg_re]
      linarith
    have hne' : e.weight ≠ d.weight ∨ e.exponent ≠ d.exponent := by
      rcases hne with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)
    obtain ⟨S, hSbij, hS⟩ := exists_bijective_embedding pre post e d hirr hn'
      hre' hne' fun h => hlink (isComplexLinked_symm h)
    exact ⟨S, hSbij, ComplexPermutation.intertwining_of_embedding hS⟩

end Langlands.Archimedean
