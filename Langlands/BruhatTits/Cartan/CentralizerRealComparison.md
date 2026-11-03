# Real evaluation of actual character restriction to a split torus

Author: Worker 1381.

This module supplies the real-space comparison used for
`CentralizerValuationComparisonStatement`. It identifies the actual real
cocharacter space `V(S)` with the real dual of the rational characters of `Z`.
It needs two inputs: `S` is an actual split torus, and character restriction
along `s : S → Z` is injective with finite-index range. Both inputs are explicit
hypotheses. The module proves neither the reductivity of a torus centralizer, nor
that `s` is its split component, nor the injectivity of character restriction.
The declared definition of this unit is `restrictionEvaluationEquiv`, the
resulting real-linear equivalence.

## Notation

For a commutative group scheme `S` over `Spec F`, `RealTorusSpace.V S` is the
real cocharacter space `ℝ ⊗_ℤ X_*(S)`. `RealTorusSpace.Vstar S` is the real
character space `ℝ ⊗_ℤ X^*(S)`, and `RealTorusSpace.pair S` is their real
bilinear pairing. `RealTorusSpace.eval S χ v` evaluates an integral character `χ`
at `v`. The published `restrictionEvaluation s` sends `v ∈ V(S)` to the additive
homomorphism `χ ↦ eval S (characterRestriction s χ) v` on the rational
characters of `Z`. Here `characterRestriction s` is actual restriction
`characterRestrict s` followed by the identification
`rationalCharacters.equivCharacterLattice S` of rational characters of `S` with
its character lattice.

## Results

- `pair_tmul_eq_mul_eval r χ v`: the real character `r ⊗ χ` pairs with `v`
  to `r * eval S χ v`. Write `r ⊗ χ` as `r • (1 ⊗ χ)` and apply the existing
  `RealTorusSpace.eval_eq_pair`.
- `eq_zero_of_eval_eq_zero hS hv`: if `S` is an actual split torus
  (`IsSplitTorus S.toGrp`) and every integral character evaluates to zero at
  `v`, then `v = 0`. The published `RealTorusSpace.isPerfPair_of_isSplitTorus`
  makes `pair S` a perfect pairing, so its flip is injective. Real-linear maps
  out of `ℝ ⊗_ℤ X^*(S)` are determined on pure tensors `r ⊗ χ`, and the first
  lemma reduces these values to `r * eval S χ v = 0`.
- `exists_eval_eq hS ℓ`: on an actual split torus, every additive real
  functional `ℓ` on the character lattice is evaluation at some `v ∈ V(S)`.
  Extend `ℓ` to the real-linear functional on `ℝ ⊗_ℤ X^*(S)` sending
  `r ⊗ χ` to `r * ℓ χ`. Surjectivity of the flipped perfect pairing gives `v`,
  and evaluating at `1 ⊗ χ` gives the claim.
- `restrictionEvaluation_id_bijective hS`: for the identity of an actual split
  torus, `restrictionEvaluation (𝟙 S)` is bijective. Since `characterRestrict`
  of the identity is the identity, `restrictionEvaluation (𝟙 S) v ψ` is the
  evaluation of the corresponding lattice character at `v`. Injectivity follows
  from `eq_zero_of_eval_eq_zero`, after transporting each lattice character back
  to a rational character. Surjectivity follows from `exists_eval_eq` applied
  to `ℓ` composed with the inverse of that identification.
- `restrictionEvaluation_eq_realCharacterDualMap s v`: for any `s : S → Z`,
  `restrictionEvaluation s v` equals the published covariant dual map
  `Global.AdelicGroupPoints.realCharacterDualMap F S Z s`, which precomposes
  with `characterRestrict s`, applied to `restrictionEvaluation (𝟙 S) v`. Both
  sides evaluate `characterRestrict s χ` at `v`.
- `restrictionEvaluation_bijective hS s hinj`: the main result. Assume `S` is an
  actual split torus, `characterRestrict s` is injective, and its range has
  finite index (instance argument). Then
  `restrictionEvaluation s : V(S) → Hom_ℤ(X^*(Z), ℝ)` is bijective.
  By the previous lemma it is `realCharacterDualMap F S Z s` composed with
  `restrictionEvaluation (𝟙 S)`. The first map is the forward function of the
  published continuous real-linear equivalence
  `Global.AdelicGroupPoints.realCharacterDualRestrictionEquiv F Z S s hinj`.
  The composite of two bijections is bijective.
- `restrictionEvaluationEquiv hS s hinj`: under the same hypotheses, the
  real-linear equivalence `V(S) ≃ₗ[ℝ] (rationalCharacters Z →+ ℝ)` obtained by
  `LinearEquiv.ofBijective` from `restrictionEvaluation s` and the previous
  theorem. `restrictionEvaluationEquiv_apply` records that its forward map is
  `restrictionEvaluation s`.

`restrictionEvaluation_id_bijective hS` is also the hypothesis `hS` of the
published `torusValuationRestriction_eq_id` in `CentralizerTorusValuation`, so for
an actual split torus that hypothesis is now a theorem.

The index-normalized extension inverse is reused from
`realCharacterDualRestrictionEquiv` and is not reconstructed here. Every
statement holds over an arbitrary field `F` at any universe `u`. Nothing
requires a local field.

## Provenance and boundary

This is a derived real-coefficient form of the comparison in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §2.6(d), printed p.103/PDF134.
There the restriction `X^*(G)^Θ → X^*(A_G)` is injective with finite-index
image, so `Hom_ℤ(X^*(G)^Θ, ℚ) = Hom_ℤ(X^*(A_G), ℚ) ≃ ℚ ⊗_ℤ X_*(A_G)` (before
(2.6.4)). The present module replaces `ℚ` by `ℝ`, the rational characters of
`Z` by the published `rationalCharacters Z`, and the split torus `A_G` by an
actual split torus `S` with a homomorphism `s : S → Z`. The duality
`Hom_ℤ(X^*(S), ℝ) ≃ ℝ ⊗_ℤ X_*(S)` is the published perfect pairing for actual
split tori. The finite-index step is the published
`realCharacterDualRestrictionEquiv`. Thus the lemmas themselves are internal
algebra; only the shape of the comparison comes from KP.

These lemmas are support for the exact target
`Langlands.BruhatTits.Cartan.CentralizerValuationComparisonStatement`. They do
not prove that target. Applying them there still requires three facts: that `S`
is a split torus (from `IsMaximalSplitTorus i`), that `characterRestrict s` has
finite-index range (from `s` being the split component of the connected
reductive centralizer `Z`), and that it is injective. Bijectivity is a statement
about real spaces only. It gives no identification of the actual valuation
image with the integral cocharacter lattice and no rank, index or Cartan
conclusion.
