# A derivation test for quotients of regular local rings

This helper module for the proof of
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` gives a criterion,
in terms of derivations into a vector space over the residue field, for a
quotient of a regular local ring to be regular. All declarations are in the
namespace `Langlands.CommutativeAlgebra.FiniteTypeIntGRing`.

Throughout, `R` is a local ring with maximal ideal `𝔪` and residue field
`κ`, and `V` is a `κ`-vector space. A derivation `R → V` (over `ℤ`, for the
`R`-module structure of `V` through `κ`) is encoded as a ring map
`Ψ : R →+* TrivSqZeroExt κ V` into the trivial square-zero extension
`κ ⊕ V` whose first component is the residue map (hypothesis
`hΨ : ∀ x, (Ψ x).fst = residue R x`). The derivation is then
`x ↦ (Ψ x).snd`; multiplicativity of `Ψ` is the Leibniz rule.

## Statements

- `trivSqZeroExt_snd_eq_zero_of_mem_sq Ψ hΨ hz`: such a derivation vanishes on
  `𝔪²`.
- `trivSqZeroExt_snd_mul_of_mem Ψ hΨ a hx`: for `x ∈ 𝔪` and any `a ∈ R`, the
  derivative of `a x` is `residue a • (derivative of x)`.
- `toCotangent_sum_mul f hfm a`: for a finite family `f` in `𝔪` and
  coefficients `a`, the class of `∑ a i * f i` in `𝔪/𝔪²` is
  `∑ residue (a i) • [f i]`.
- `linearIndependent_toCotangent_iff f hfm`: the classes of the `f i` in
  `𝔪/𝔪²` are linearly independent over `κ` if and only if every relation
  `∑ a i * f i ∈ 𝔪²` has all coefficients `a i` in `𝔪`.
- `isRegularLocalRing_quotient_of_trivSqZeroExt Ψ hΨ f hfm hf` (**derivation
  test**): let `R` be a regular local ring, `V` a `κ`-vector space (with the
  same left and right action, `IsCentralScalar`), `Ψ` as above, and `f` a
  finite family in `𝔪`. If the derivatives `(Ψ (f i)).snd` are linearly
  independent over `κ`, then `R ⧸ (f i : i ∈ ι)` is a regular local ring.

The derivation test is the local form of the Jacobian criterion: elements
whose differentials are independent form part of a regular system of
parameters. The module is internal to the project's proof and does not follow
a specific reference.

## Proofs

**Vanishing on `𝔪²`.** By induction on membership in `𝔪 · 𝔪`
(`Submodule.mul_induction_on`). For a product `x y` with `x, y ∈ 𝔪`,
`TrivSqZeroExt.snd_mul` gives
`(Ψ (x y)).snd = residue x • (Ψ y).snd + residue y • (Ψ x).snd`, and both
residues vanish. Sums are handled by additivity.

**Linearity on `𝔪`.** The same formula for `a x`, with `residue x = 0`.

**Classes of linear combinations.** The element `∑ a i * f i` of `𝔪` is
`∑ a i • f i` in the `R`-module `𝔪`. `Ideal.toCotangent` is `R`-linear, and
the action of `R` on `𝔪/𝔪²` factors through `κ` (`algebraMap_smul`).

**Cotangent independence.** By `Fintype.linearIndependent_iff`,
independence means that `∑ g i • [f i] = 0` forces all `g i = 0`.
(⇒) Given `∑ a i * f i ∈ 𝔪²`, its class is zero
(`Ideal.toCotangent_eq_zero`), so with `g i = residue (a i)` all residues
vanish, that is `a i ∈ 𝔪`. (⇐) Given a relation with coefficients
`g i ∈ κ`, lift them to `a i ∈ R` (`residue_surjective`). The class of
`∑ a i * f i` is then zero, so it lies in `𝔪²`, hence every `a i ∈ 𝔪` and
every `g i = 0`.

**Derivation test.** By `isRegularLocalRing_quotient_span_of_linearIndependent`
(module `RegularQuotient`), it suffices that the classes of the `f i` in
`𝔪/𝔪²` are independent, and by the previous statement that every relation
`∑ a i * f i ∈ 𝔪²` has coefficients in `𝔪`. For such a relation, the
derivative of `∑ a i * f i` vanishes (first statement). Expanding with
`map_sum`, `TrivSqZeroExt.snd_sum` and the second statement gives
`∑ residue (a i) • (Ψ (f i)).snd = 0`. Independence of the derivatives forces
`residue (a i) = 0`, that is `a i ∈ 𝔪`.
