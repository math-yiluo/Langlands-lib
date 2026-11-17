# The bridge premise from an analytic premise

Module `Langlands.Global.RankinSelberg.ComplexPlaceWhittakerBridge`, namespace
`Langlands.Global.RankinSelbergGlobal`. Worker 5665 wrote it for Task 7399 (prove
`ComplexPlaceFunctionalEquationStatement`, Jacquet 2009, Theorem 2.1, at a complex place). It
is a conditional reduction: it proves implications from premises that stay open. Provenance:
internal.

The module `ComplexPlaceFunctionalEquationReduction` proves the target from five open
premises. One of them is the bridge `ComplexPlaceWhittakerModelStatement`: every archimedean
restriction `g ↦ W_x(ι_w(g) b)` of a global Whittaker function of an actual cuspidal
realization `T` with parameter `d` at the complex place `w` lies in `complexWhittakerModel r d a`
(for `ψ`, with component `ψ_a` at `w`), and the one for `ψ⁻¹` lies in
`complexWhittakerModel r d (-a)`. This module replaces the bridge in two steps:

1. by the per-map premise `ComplexPlaceWhittakerIntertwinerStatement`, about one
   `(𝔤, K)`-map at a time (algebraic step: `complexPlaceIsotypic_eq_top`);
2. by the analytic premise `ComplexPlaceWhittakerAnalyticStatement`, about the restriction of a
   single vector (the `θ`- and `U(r+1)`-equivariance clauses are proved in
   `ComplexPlaceWhittakerEquivariance`).

The final result is `complexPlaceFunctionalEquationAnalyticReduction`: the target follows from
the two local functional equations, the analytic premise, the minus-one premise and the
contragredient premise.

## The per-map premise

`ComplexPlaceWhittakerIntertwinerStatement`. Let

* `F` be a number field with compact adele quotient;
* `ψ` a unitary character of `𝔸_F` trivial on `F` (`ψ (algebraMap F _ x) = 1`);
* `T` an actual cuspidal realization of `GL_(r+1)` over `F`;
* `w` a complex place and `a ∈ ℂˣ` with `IsComplexAdditiveComponent ψ w a`, i.e. the
  component of `ψ` at `w` is `ψ_a = complexScaledCharacter a`;
* `d` a list of complex characters, and `A` a `(𝔤, K)`-map at `w` from the `U(r+1)`-finite
  standard module of `d` into `T` (`IsComplexPlaceMap`, module `ComplexPlaceIsotypic`);
* `b` a finite adelic point.

Then there is a `ℂ`-linear map `B` from the `U(r+1)`-finite standard module of `d` to functions
on `GL_(r+1)(ℂ)` with `IsComplexWhittakerIntertwiner r d a B` and
`B f = (g ↦ cuspWhittaker F T ψ.complex (A f) (ι_w(g) b))` for every `f`. Likewise there is
one with `IsComplexWhittakerIntertwiner r d (-a) B` and
`B f = (g ↦ cuspWhittaker F T ψ.complex⁻¹ (A f) (ι_w(g) b))`. Here `ι_w(g) b` is
`complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b`, and `cuspWhittaker` is the
Library's global Whittaker coefficient `W_x(h) = ∫_(N(F)\N(𝔸)) φ_x(n h) θ(n)⁻¹ dn`.

The premise is stated with an existential `B`, so linearity of `f ↦ B f` is part of what it
asserts. It holds because `cuspWhittaker` is linear in the vector (Library
`UnramifiedWhittaker.cuspWhittaker_add`, `cuspWhittaker_smul`) and `A` is linear.

## The analytic premise

`ComplexPlaceWhittakerAnalyticStatement`. Let `F` be a number field with compact adele
quotient, `χ` a standard additive character of `𝔸_F` (`IsStandardAdditiveCharacter`: continuous,
nontrivial, trivial on `F`, of absolute value `1`), `T` an actual cuspidal realization of
`GL_(r+1)`, `w` a complex place, `b` a finite adelic point and `x` a vector of `T`. Put
`W(g) = W_x(ι_w(g) b)` (`cuspWhittaker F T χ x`). Then:

1. `W` is smooth (`ContMDiff` of all orders for the Library's manifold structure
   `matrixModel ℂ (r + 1)` on `GL_(r+1)(ℂ)`);
2. there are `C` and `N` with `|W(g)| ≤ C ‖g‖_H^N` for every `g`, where `‖g‖_H` is Jacquet's
   height `complexMatrixHeight` (Jacquet 2009, (2.1));
3. for every real direction `X ∈ 𝔤𝔩_(r+1)(ℂ)`, the restriction of the Lie action
   `complexPlaceLieAction w (1 ⊗ X) x` is the right derivative of `W` along `X`
   (`Archimedean.rightDerivative (matrixModel ℂ (r + 1)) X W`).

### Why the analytic premise is expected to hold

Put `φ` for the automorphic form of `x`.

1. **Smoothness.** Automorphic forms are smooth at `w`, and the Whittaker integral is over the
   compact quotient `N(F)\N(𝔸)` with a continuous integrand, so it can be differentiated under
   the integral sign any number of times.
2. **Polynomial growth**, with `C` and `N` depending on `x`. No unitary central character is
   assumed, so `φ` need not be bounded. (For `GL_1` over an imaginary quadratic field, the
   realization by the normalized idelic norm has Whittaker restriction `|z|²`, which is
   unbounded but is at most `‖z‖_H = |z|² + |z|⁻²`.) `φ` is an automorphic form, so on each slice
   it is bounded by `C_(b') H(a)^(d_(b'))`, with `H` the Library's archimedean height
   (`IsAutomorphicForm`, `HasPolynomialGrowth`). The Whittaker integral can be taken over a
   compact set `Ω_∞ × Ω_f` of representatives, and `|χ| = 1`. `φ` is right invariant under an
   open compact subgroup, so the compact set `Ω_f b` meets only finitely many slices. Also
   `H(n_∞ a) ≤ c H(a)` for `n_∞ ∈ Ω_∞`, and `H(ι_w(g)) ≤ c' ‖g‖_H`, since the entries of `g` and
   `g⁻¹` are bounded by `‖g‖_H^(1/2)` and `‖g‖_H ≥ 2`. Hence `|W(g)| ≤ C ‖g‖_H^N`.
3. **Lie compatibility.** The Lie action of `X` at `w` on `φ` is the derivative of `φ` along
   the one-parameter subgroup `ι_w(exp(t X))` acting on the right. Differentiating under the
   integral sign gives the right derivative of `W` along `X`.

The per-map premise also contains `θ`-equivariance and `U(r+1)`-equivariance. These are
proved in `ComplexPlaceWhittakerEquivariance` and are not part of the analytic premise.

## Results

- `restriction_mem_complexWhittakerModel`: let `χ` be a standard additive character
  (`IsStandardAdditiveCharacter`), `b` a finite adelic point, and assume that for every
  `(𝔤, K)`-map `A` the map `f ↦ (g ↦ W_(A f)(ι_w(g) b))` (for `χ`) is given by a Whittaker
  intertwiner for `a`. Then for every `x` in `complexPlaceIsotypic T w d` (the sum of the
  images of all `(𝔤, K)`-maps), `g ↦ W_x(ι_w(g) b)` lies in `complexWhittakerModel r d a`.
  Proof by induction over the supremum (`Submodule.iSup_induction'`):
  * for `x = A f` the function is `B f`, in the range of the intertwiner `B`, which is
    contained in the model by definition (a supremum of ranges);
  * for `x = 0` the function is `0` (`cuspWhittaker_smul` with scalar `0`);
  * for `x = y + z` the function is the sum (`cuspWhittaker_add`, which uses that `χ` is
    standard), and the model is a submodule.
- `complexPlaceWhittakerModelReduction : ComplexPlaceWhittakerModelReductionStatement`, i.e.
  `ComplexPlaceWhittakerIntertwinerStatement → ComplexPlaceWhittakerModelStatement`. Given
  `W = (g ↦ W_x(ι_w(g) b))` with `x ∈ T`:
  * `ψ.complex` is standard (Library `isStandardAdditiveCharacter_of_unitary`), and so is
    its inverse (Library `Unfolding.isStandardAdditiveCharacter_inv`);
  * every `x` lies in `complexPlaceIsotypic T w d`, because that sum is all of `T`
    (`complexPlaceIsotypic_eq_top`, from irreducibility of `T` and its parameter `d` at `w`);
  * `restriction_mem_complexWhittakerModel` with the premise for `ψ` and `a`, and for `ψ⁻¹`
    and `-a`, gives the two claims of the bridge.
- `complexPlaceFunctionalEquationIntertwinerReduction :
  ComplexPlaceFunctionalEquationIntertwinerReductionStatement`, i.e. the target
  `ComplexPlaceFunctionalEquationStatement` follows from
  `ComplexLocalUnequalFunctionalEquationStatement`,
  `ComplexLocalEqualFunctionalEquationStatement`, `ComplexPlaceWhittakerIntertwinerStatement`,
  `ComplexPlaceMinusOneStatement` and `ComplexPlaceContragredientParameterStatement`. It is
  `complexPlaceFunctionalEquationReduction` with the bridge supplied by
  `complexPlaceWhittakerModelReduction`.

- `exists_restriction_isComplexWhittakerIntertwiner`: assume the analytic premise. Let `χ` be
  standard with `χ((Pi.single w y, 0)) = ψ_c(y)` (the component of `χ` at `w` is `ψ_c`), and
  `A` a `(𝔤, K)`-map at `w`. Then `f ↦ (g ↦ W_(A f)(ι_w(g) b))` is a `ℂ`-linear map `B` (by
  `cuspWhittaker_add` and `cuspWhittaker_smul`) with `IsComplexWhittakerIntertwiner r d c B`:
  * clause 1 (`θ`-equivariance) is `complexPlaceRestriction_mul_left`;
  * clauses 2 and 3 (smoothness, growth) are the analytic premise for the vector `A f`;
  * clause 4 (`U(r+1)`) is `complexPlaceRestriction_rightTranslation`;
  * clause 5 (Lie): if `f'` is the right derivative of `f` along `X`, then `A f'` is the Lie
    action of `1 ⊗ X` at `w` on `A f` (the second clause of `IsComplexPlaceMap`), and the
    analytic premise for `A f` gives that `B f'` is the right derivative of `B f`.
- `complexPlaceWhittakerIntertwinerReduction : ComplexPlaceWhittakerIntertwinerReductionStatement`,
  i.e. `ComplexPlaceWhittakerAnalyticStatement → ComplexPlaceWhittakerIntertwinerStatement`. Apply
  the previous item to `χ = ψ.complex` with `c = a` (`complexComponent_complex`) and to
  `χ = ψ.complex⁻¹` with `c = -a` (`complexComponent_complex_inv`).
- `complexPlaceFunctionalEquationAnalyticReduction :
  ComplexPlaceFunctionalEquationAnalyticReductionStatement`, i.e. the target
  `ComplexPlaceFunctionalEquationStatement` follows from
  `ComplexLocalUnequalFunctionalEquationStatement`,
  `ComplexLocalEqualFunctionalEquationStatement`, `ComplexPlaceWhittakerAnalyticStatement`,
  `ComplexPlaceMinusOneStatement` and `ComplexPlaceContragredientParameterStatement`. It is
  `complexPlaceFunctionalEquationIntertwinerReduction` with the per-map premise supplied by
  `complexPlaceWhittakerIntertwinerReduction`.

None of the five premises is proved here. The required unconditional proof of
`ComplexPlaceFunctionalEquationStatement` stays open.
