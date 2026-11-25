# Non-largeness of linked Langlands quotients from a small submodule of the dual

Lean module: `Langlands.Representation.Archimedean.ComplexLinkedLanglandsQuotientDuality`
(namespace `Langlands.Archimedean`; helpers in `Langlands.Archimedean.ComplexLinkedLanglandsQuotientDuality`).

This module states `ComplexDualSubmoduleAnnihilatorStatement` and proves that it implies the
Library statement `ComplexLinkedLanglandsQuotientNotLargeStatement` (module
`ComplexLargeStandardIrreducibleSplit`). It does not prove `ComplexDualSubmoduleAnnihilatorStatement`.

Notation: `I(ds)` is `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`, the
`U(n)`-finite functions of the standard module of `ds`. Its `(𝔤, K)`-structure is
`complexStandardRep n ds` (right translation by `U(n)`) and `complexStandardLie n ds` (right
derivatives, extended `ℂ`-linearly to `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`). `U(𝔤)` is
`UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)`, acting through
`envelopingAction` (Library `RealGenericLargeReduction`).

## The statement

```lean
def ComplexDualSubmoduleAnnihilatorStatement : Prop :=
  ∀ (n : ℕ) (ds ds' : List ComplexCharacterData), ds.length = n → IsComplexLanglandsOrdered ds →
    ¬ IsComplexUnlinked ds →
    (∀ (i : ℕ) (z : ℂˣ), complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1) →
      ∃ S : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
        IsGKSubmodule (complexStandardRep n ds') (complexStandardLie n ds') S ∧ S ≠ ⊥ ∧
        ∃ u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ),
          (∀ s ∈ S, envelopingAction (complexStandardLie n ds') u s = 0) ∧
          envelopingAction (complexStandardLie n ds') u ≠ 0
```

Take a list `ds` of `n` complex characters. Assume it is in Langlands order
(`IsComplexLanglandsOrdered`, Library `ComplexGenericParameterReduction`) and that two of its
characters are linked (`¬ IsComplexUnlinked ds`, Library `ComplexLargeStandardIrreducibleSplit`).
Let `ds'` be a list whose position characters are pointwise inverse to those of `ds`. These are
exactly the hypotheses of the Library's `ComplexStandardDualityStatement`. The statement says
that `I(ds')` has a nonzero `(𝔤, K)`-submodule `S` and an element `u ∈ U(𝔤)` that acts by `0`
on `S` but not on all of `I(ds')`. In other words, `Ann_{U(𝔤)}(S) ≠ Ann_{U(𝔤)}(I(ds'))`.

### Provenance and why it holds

This is an internal intermediate statement of the proof of
`ComplexLinkedLanglandsQuotientNotLargeStatement` (module
`ComplexLinkedLanglandsQuotientNotLargeProof`). It is a submodule form of the
non-largeness of the Langlands quotient and is not quoted from a source. Under the duality
`I(ds) × I(ds') → ℂ`, the Langlands quotient `I(ds)/R` corresponds to the unique irreducible
submodule of `I(ds')`. For a linked pair this submodule is small: when the pair is adjacent
and suitably ordered, it lies in a module induced from a finite-dimensional representation
`F_p ⊠ F̄_q` of a `GL_2(ℂ)` block. Its annihilator is then strictly larger than that of the
principal series (Vogan 1978, Lemma 6.5 and Corollary 6.6, p. 94, in Gelfand–Kirillov
dimension form). The Library proves this statement by a Gelfand–Kirillov growth comparison
(`complexDualSubmoduleAnnihilator_of_growth`, module `ComplexLinkedLanglandsQuotientGrowth`,
applied in `ComplexLinkedLanglandsQuotientNotLargeProof`). It is not part of this module.

## The reduction

`complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule :
ComplexDualSubmoduleAnnihilatorStatement → ComplexLinkedLanglandsQuotientNotLargeStatement`.

Let `n`, `ds` and `R` be as in `ComplexLinkedLanglandsQuotientNotLargeStatement`, and assume
`IsMaximallyFaithfulModulo (complexStandardLie n ds) R`. The proof derives a contradiction.

1. **The dual list.** `ds' = ds.map complexCharacterDataInv` replaces every character by its
   inverse (Library `complexCharacterDataInv`, module `ComplexLanglandsQuotientReduction`:
   weight `-l`, exponent `-t`, character `χ⁻¹`). The Library lemma
   `complexPositionCharacter_map_inv_mul`, with the factors commuted, shows that its position
   characters are pointwise inverse to those of `ds`.
2. **Duality.** The Library theorem `complexStandardDuality` gives a bilinear form
   `Q : I(ds) × I(ds') → ℂ`. It is invariant under `U(n)`, satisfies
   `Q(R(X) f, h) + Q(f, R(X) h) = 0` for `X ∈ 𝔤𝔩_n(ℂ)`, and is nondegenerate in the second
   argument. `pairing_lie` extends the Lie invariance to all of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` by induction on
   tensors. It uses `c ⊗ X = c • (1 ⊗ X)` and `lie_one_tmul_eq`, which identifies
   `complexStandardLie n ds (1 ⊗ X)` with the right derivative along `X`
   (`principalSeriesLie_one_tmul_apply_coe`).
3. **The submodule.** Applying the hypothesis to `ds` and `ds'` gives `S` and `u`. Let
   `K' = {f ∈ I(ds) : Q(f, s) = 0 for all s ∈ S}`.
   - `K'` is `U(n)`-stable. For `k ∈ U(n)`, `Q(k f, s) = Q(k f, k (k⁻¹ s)) = Q(f, k⁻¹ s) = 0`,
     and `k⁻¹ s ∈ S`.
   - `K'` is `𝔤`-stable. `Q(X f, s) = -Q(f, X s) = 0`, and `X s ∈ S`.
   - `K' ≠ ⊤`. Pick `s ≠ 0` in `S`. Nondegeneracy gives `f` with `Q(f, s) ≠ 0`, so `f ∉ K'`.

   By the hypothesis on `R`, every proper `(𝔤, K)`-submodule lies in `R`, so `K' ≤ R`.
4. **Transpose.** `transpose : U(L) →ₐ[ℂ] U(L)ᵐᵒᵖ` is the principal anti-automorphism. It is
   the lift of the Lie algebra map `negOp : x ↦ op(-x)`. `tr u` is its value read back in
   `U(L)`, and it satisfies `tr (a b) = tr b · tr a` and `tr x = -x` for `x ∈ L`. For any
   bilinear form `B` with `B(x v, w) + B(v, x w) = 0` on `L`, `bilin_envelopingAction` proves
   `B(v, u w) = B(tr(u) v, w)` for every `u ∈ U(L)`. The proof is induction on `u` with the
   Library principle `InfinitesimalCharacter.envInduction`: scalars, generators, products and
   sums.
5. **Conclusion.** Put `w = tr u`. For `f ∈ I(ds)` and `s ∈ S`,
   `Q(w f, s) = Q(f, u s) = 0`, so `w f ∈ K' ≤ R`. The standard module of `ds` has an
   infinitesimal character (Library `complexStandardLie_hasInfinitesimalCharacter`) and
   `R ≠ ⊤`. So `MaximallyFaithfulAnnihilator.envelopingAction_eq_zero` (Library) gives that
   `w` acts by `0` on `I(ds)`. But `u` acts nonzero on some `h ∈ I(ds')`. Nondegeneracy gives
   `f` with `0 ≠ Q(f, u h) = Q(w f, h) = Q(0, h) = 0`, a contradiction.

The hypothesis that `R` is itself a `(𝔤, K)`-submodule is not used.
