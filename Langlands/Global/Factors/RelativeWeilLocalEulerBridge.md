# Rank-one L-factors of the local virtual identity as Tate's L-factors

This module continues `RelativeWeilLocalEuler`. That module computes the
arithmetic pair L-factor of two zero-monodromy pairs `V`, `W` of a p-adic
field `F` from a local virtual identity

`[T] = d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])`, `T ≃ V ⊗ W`.

The result there is a formal rational function in `RatFunc ℂ`, built from the
classical Euler polynomials of the Weil characters `α₀`, `α_j`, `β_j`. This
module does three things.

1. When the characters are Weil characters `η ∘ e` of quasicharacters `η`
   along geometric reciprocity candidates `e`, it rewrites those factors as
   Tate's L-factors of the quasicharacters (`PadicAbelian.lPolynomial`,
   `rationalLFactor`).
2. It evaluates the formal identity at the spectral point `q_F^{-s}`. The
   result is the complex number `virtualLValue`, a product of Tate's
   `L(s, ·)` over `F` and the `E_j`. This holds at every `s` where the rank-one
   L-factors involved are finite.
3. It moves Tate's L-factors and epsilon factors between two realizations of
   a completion `K_w` of a number field. One is the completion realization
   `CompletionPadic.topologicalData w`, used by Hecke's local factors. The
   other is the canonical realization of its p-adic package
   `padicFieldAt w h`, used by the local Weil group side. It also identifies
   the trace character of the standalone tower extension with the base
   character composed with the local trace.

## Provenance

The provenance is derived. The rank-one L-factor is Tate's
*Number theoretic background* (Corvallis 1979), (3.1.3), printed p. 13
(PDF p. 22): `L(χ) = (1 - χ(π))^{-1}` if `χ` is unramified and `1`
otherwise, in the Library's form `PadicAbelian.lFactor`. Tate's §3.3,
printed p. 14 (PDF p. 23), requires that the Weil group L-factor (3.3.2) of
a degree-one representation be `L(χ)` for the corresponding quasicharacter.
`characterEulerPolynomial_weilCharacter` proves this for the Library's
definitions, with the reciprocity law given by a geometric candidate `e`.
Tate's epsilon factors (§3.2, printed pp. 13–14) enter only through the
transport lemmas, which say that they do not depend on the choice of equal
realization. Everything else is internal bookkeeping: evaluation of rational
functions at a point, and equalities of topologies and of realizations from
the Library's `CompletionPadic.completion_topology_eq`.

## Rank-one L-factors (`Langlands.Weil.Local.InertiaEuler`)

A local instance gives each p-adic package its canonical topology.

- `characterEulerPolynomial_weilCharacter`: for a geometric reciprocity
  candidate `e` of `F` and a quasicharacter `η`,
  `characterEulerPolynomial F (weilCharacter F e η)` is Tate's Euler
  polynomial `PadicAbelian.lPolynomial F.canonicalTopologicalData η`. The
  proof splits on the conductor of `η`. The Library's
  `isUnramifiedQuasicharacter_iff_isUnramifiedCharacter` and
  `weilCharacter_trivial_on_inertia_iff` match unramifiedness on the two
  sides. In the unramified case, `weilCharacter_localGeometricFrobenius`
  identifies the Frobenius value with `η(π)`.
- `inducedLFactor_weilCharacter`: the L-factor over `F` of the character
  induced along `extensionWeilMap F E g` from `weilCharacter E e η` is
  `(P(X^f))^{-1}`, where `P` is Tate's Euler polynomial of `η` over `E` and `f`
  the residue degree.
- `characterLFactor_weilCharacter`: `characterLFactor F (weilCharacter F e η)`
  is Tate's `PadicAbelian.rationalLFactor` of `η`.

## Evaluation at the spectral point

- `IsRegularUnitAt x r`: the rational function `r` is `N / D` for
  polynomials `N`, `D` neither of which vanishes at `x`. The namespace
  `IsRegularUnitAt` proves that this property is closed under `1`, products,
  inverses, quotients, natural and integer powers and finite products. It
  also proves that evaluation at `x` (`RatFunc.eval (RingHom.id ℂ) x`) is
  multiplicative on such functions and gives a nonzero value
  (`eval_ne_zero`).
- `eval_algebraMap_div_algebraMap`, `isRegularUnitAt_inv_algebraMap`,
  `eval_inv_algebraMap`: evaluation of `N / D` and of `P^{-1}` where the
  denominator does not vanish. The first is the Library's
  `RankinSelberg.regular_and_eval_div`.
- `lFactor_eq_inv_eval`: Tate's `L(s, η)` is the inverse of the value of its
  Euler polynomial at the spectral variable `q^{-s}`; at a pole both sides are
  `0`. Hence `eval_lPolynomial_ne_zero`: where `L(s, η) ≠ 0`, the Euler
  polynomial does not vanish at `q^{-s}`.
- `spectralPoint_eq_spectralVariable`: the spectral point
  `spectralPoint q_F s` is Tate's spectral variable of `F` at `s` (the
  Library's `GodementJacquet.Padic.tate_spectralPoint_eq`).
- `isRegularUnitAt_characterLFactor_weilCharacter`,
  `eval_characterLFactor_weilCharacter`: where `L(s, η) ≠ 0`, the L-factor of
  `weilCharacter F e η` is a regular unit at `q_F^{-s}`, and its value there is
  `L(s, η)`.
- `eval_expand_lPolynomial`: the polynomial `P(X^f)` over `F` at `q_F^{-s}` has
  the value of `P` at the spectral variable of `E` at `s`; this is the Library's
  `extensionExpandedPolynomial_eval`.
- `isRegularUnitAt_inducedLFactor_weilCharacter`,
  `eval_inducedLFactor_weilCharacter`: where Tate's `L(s, η)` over `E` is
  nonzero, the induced L-factor is a regular unit at `q_F^{-s}` with value
  `L(s, η)` over `E`.
- `virtualLValue F χ₀ d E η η' n s` (the selected definition): the complex
  number `L(s, χ₀)^d Π_j (L(s, η_j) / L(s, η'_j))^{n_j}`, with Tate's
  L-factors of `F` and of the `E_j`.
- `eval_arithmeticPairLFactor_eq_virtualLValue` (main theorem). Let `T` be
  continuous with carrier universe `max u w`, with `T ≃ V ⊗ W`. Suppose that
  in the continuous exact virtual group of `W_F`
  `[T] = d • [η₀ ∘ e₀] + Σ_j n_j • Ind_{g_j}([η_j ∘ e_j] - [η'_j ∘ e_j])`,
  written with `χ₀` for `η₀`. Here `e₀` and the `e_j` are geometric
  reciprocity candidates of `F` and of the `E j`, and `Ind_{g_j}` is
  `continuousInduceAlong` along `extensionWeilMap F (E j) (g j)`. Let `s` be a
  point where `L(s, χ₀)`, `L(s, η_j)` and `L(s, η'_j)` are all nonzero. Then
  the arithmetic pair L-factor of the zero-monodromy pairs of `V` and `W`,
  evaluated at `q_F^{-s}`, is `virtualLValue F χ₀ d E η η' n s`. The proof
  rewrites with `arithmeticPairLFactor_eq_of_virtualIdentity` and evaluates
  each factor with the lemmas above.
- `weilCharacter_inv'`: the inverse of `weilCharacter K e η` is
  `weilCharacter K e η⁻¹`.
- `eval_arithmeticPairLFactor_dual_eq_virtualLValue`: under the same identity,
  for `Vd ≃ V^∨` and `Wd ≃ W^∨`, at a point where the L-factors of the inverse
  quasicharacters are nonzero, the arithmetic pair L-factor of the
  zero-monodromy pairs of `Vd` and `Wd` at `q_F^{-s}` is `virtualLValue` of the
  inverse quasicharacters. The proof applies the contragredient to the
  identity and uses the main theorem for `T^∨ ≃ Vd ⊗ Wd`.

## Equal realizations (`Langlands.LocalFactor.PadicAbelian`)

- `topologicalData_ext`: two realizations of a p-adic package with the same
  topology and the same valuative relation are equal; the remaining fields
  are proofs.
- `quasicharacterCongr`, `unitaryCharacterCongr`, `haarMeasureCongr`: a
  quasicharacter, a unitary additive character or an additive Haar measure
  for one topology, seen as one for an equal topology. The underlying
  homomorphism, additive character or measure is unchanged.
- `lFactor_quasicharacterCongr`: Tate's L-factor is the same for two equal
  realizations and the transported quasicharacter.
- `epsilon_quasicharacterCongr`: Tate's fixed-Haar epsilon factor
  `PadicAbelian.epsilon` is the same for two equal realizations, the
  transported quasicharacter and Haar measure, and any additive character
  with the same underlying additive character.

## Completions of number fields (`Langlands.Global.CompletionPadic`)

Let `w` be a finite place of a number field `K`, with residue prime `p`
(`h : residuePrime w = p`).

- `topologicalData_eq_canonicalTopologicalData`: the completion realization
  `topologicalData w` is the canonical realization of `padicField w`.
- `padicFieldAt_topology_eq`: the completion topology is the canonical
  topology of `padicFieldAt w h`.
- `quasicharacterAt`, `additiveCharacterAt`, `haarMeasureAt`: a character of
  `K_wˣ`, a unitary additive character and an additive Haar measure of `K_w`,
  continuous for the completion topology, as a quasicharacter, a nontrivial
  additive character and a Haar measure of the canonical package
  `padicFieldAt w h`. `quasicharacterAt_toMonoidHom` and
  `additiveCharacterAt_toAddChar` say that the underlying maps are unchanged.
  `quasicharacterAt_inv` says that `quasicharacterAt` commutes with
  inversion.
- `residueCardinality_padicFieldAt`: the two realizations have the same
  residue cardinality.
- `lFactor_quasicharacterAt`: Tate's L-factor of `χ` for the completion
  realization equals that of `quasicharacterAt w h χ` for the canonical
  package.
- `epsilon_quasicharacterAt`: Tate's epsilon factor of `χ`, an additive
  character `ψ` and a Haar measure `μ` for the completion realization equals
  that of `quasicharacterAt w h χ`, any nontrivial additive character `ψE` of
  the package with the same underlying additive character as `ψ`, and
  `haarMeasureAt w h μ`.

## Trace characters

- `standaloneTraceCharacter_additiveCharacterAt`: for an extension of number
  fields `K / F` and a place `w` of `K` over a place `v` of `F`, take the
  standalone tower extension `towerPadicField v w` of `padicField v` along
  `completionPadicAlgHom v w`. The trace character
  `SystemEpsilon.standaloneTraceCharacter` of the transported base character
  `additiveCharacterAt v rfl ψ`, evaluated at `x ∈ K_w`, is
  `ψ(FiniteExtension.localTrace v w x)`. The proof is `rfl`.

These results are supporting lemmas for the global assembly of the twisted
relative Weil functional equation. No semisimplicity is assumed, and the
module does not prove the task's target statement.
