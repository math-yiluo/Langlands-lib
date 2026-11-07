# Inertia Euler polynomials on continuous virtual representations of a local Weil group

This module is the finite-place L-factor part of the local algebra for the
twisted relative Weil functional equation. Fix a p-adic field `F`, with local
Weil group `W_F`, inertia subgroup `I = localInertia F` and the Library's
geometric Frobenius lift `Fr = localGeometricFrobenius F`. For a finite
dimensional complex representation `A` of `W_F`, Tate, *Number theoretic
background* (Corvallis 1979), (3.3) and (3.3.2), printed p. 14, defines

`L(A) = det(1 - Fr | A^I)^{-1}`,

with `Fr` an inverse Frobenius. Tate's §3.3 says that this `L` is inductive
in the sense of his (2.3.2), with a proof in Deligne [D3, Prop. 3.8]. The start
of his §2, printed p. 9, notes that an additive function on representations
extends to a homomorphism on virtual representations. This module puts that L-factor in Lean as a homomorphism on the
continuous exact virtual group of `W_F`. It then computes the homomorphism on
characters and on characters induced along the Weil map of a finite extension.
The result is a formula for the arithmetic pair L-factor of two zero-monodromy
pairs `V`, `W` in terms of any virtual identity
`[T] = d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])` for a continuous `T ≃ V ⊗ W`.
A dual form of the formula is also proved. Values are formal: `X` stands for
`q^{-s}`, and the L-factor lives in `RatFunc ℂ`.

## Provenance

The provenance is derived. The definition of the L-factor is Tate's (3.3.2),
for the zero-monodromy case: the published `WeilDeligne.eulerPolynomial` uses
the inertia invariants of the monodromy kernel, and the monodromy kernel of a
zero-monodromy pair is the whole representation
(`eulerPolynomial_zeroMonodromy`). Additivity, proved here, gives the
factorisation of `lFactorHom` through the virtual group. The values on
induced characters come from the Library theorem
`LocalFactor.Inductive.eulerFactorInduction`, the Library's form of the
inductivity of the Euler factor in Tate's §3.3. All other content is
internal bookkeeping: equivalences across carrier universes, exactness of
invariants, and the compatibility of contragredients with tensor products and
induction.

## Linear algebra (`Langlands.LocalFactor`)

- `det_eq_mul_of_exact`: for a short exact sequence `0 → V → W → U → 0` of
  complex vector spaces, of which only `W` is assumed finite dimensional, and
  operators `A`, `B`, `C` compatible with the maps,
  `det B = det A * det C`. The proof identifies `V` with the kernel `N` of
  `W → U` and `W ⧸ N` with `U`. It then applies Mathlib's
  `LinearMap.det_eq_det_mul_det` to the `B`-stable submodule `N`.
- `eulerPolynomial_eq_mul_of_exact`: the same statement for the Euler
  polynomial `det(1 - X A)`, checked by evaluation at every complex number.

## Representations (`Langlands.FiniteRepresentation`)

- `invariantsEquivOfEquiv`: an equivalence `A ≃ B`, with independent carrier
  universes, restricts to an equivalence of the fixed spaces of a normal
  subgroup.
- `eulerPolynomial_invariants_eq_of_equiv`: so the Euler polynomial of any
  group element on the fixed spaces is the same for `A` and `B`.
- `invariantsMap_surjective`: suppose the normal subgroup `I` acts on `B`
  through a finite group. Then a surjective intertwining map `B → C` stays
  surjective on `I`-invariants. The proof averages a preimage over the finite
  quotient `I ⧸ ker`, using Mathlib's `Representation.averageMap`; it follows
  the pattern of the Library module `LocalFactor/InvariantsDual.lean`.
- `isShortExact_invariants`: under the same finiteness assumption on the
  middle term, the `I`-invariants of a short exact sequence form a short exact
  sequence.
- `eulerPolynomial_invariants_of_shortExact`: so the Euler polynomial on
  `I`-invariants, at any group element, is multiplicative along such a
  sequence.
- `restrictEquivOfEquiv`, `induceEquivOfEquiv`, `induceAlongEquivOfEquiv`:
  restriction, finite-index induction and induction along an injective map
  with finite-index range, applied to an equivalence whose two sides have
  different carrier universes. The Library's `restrictEquiv` and `induceEquiv`
  need a single universe.
- `characterLineUniverseEquiv`: the character lines of one character in two
  carrier universes are equivalent.
- `tensorDualEquiv`: `A^∨ ⊗ B^∨ ≃ (A ⊗ B)^∨`, by Mathlib's
  `TensorProduct.dualDistribEquiv`, which sends `f ⊗ g` to
  `x ⊗ y ↦ f x * g y`.

## Weil-Deligne pairs (`Langlands.WeilDeligneRepresentation`, `Langlands.LocalFactor.WeilDeligne`)

- `zeroMonodromyKernelEquiv`: the monodromy kernel of the zero-monodromy pair
  of `A` is all of `A`.
- `tensorZeroMonodromyEquiv`: the tensor product of the zero-monodromy pairs
  of `A` and `B` is the zero-monodromy pair of `A ⊗ B`; the identity map
  works because the tensor monodromy `N ⊗ 1 + 1 ⊗ N` is zero.
- `eulerPolynomial_zeroMonodromy`: the Weil-Deligne Euler polynomial of a
  zero-monodromy pair is the Euler polynomial on the inertia invariants of its
  representation.

## Virtual representations (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

- `continuousDual_continuousInduceAlong`: on continuous exact virtual groups,
  the contragredient commutes with induction along an open embedding with
  finite-index range. Its proof unfolds `continuousInduceAlong` as restriction
  along the range inverse followed by induction, then uses the Library's
  `continuousDual_induce` and `continuousRestrict_continuousDual`.

## The L-factor homomorphism (`Langlands.Weil.Local.InertiaEuler`)

- `eulerPolynomial F A`: `det(1 - X Fr | A^I)` for a local Weil
  representation `A` of `F`.
- `lFactorUnit F A`: its inverse, `det(1 - X Fr | A^I)^{-1}`, as a unit of
  `RatFunc ℂ`. The Euler polynomial has constant term `1`, so it is nonzero.
  `coe_lFactorUnit` gives its value.
- `eulerPolynomial_eq_of_equiv`, `lFactorUnit_eq_of_equiv`: both depend only
  on the equivalence class, even across carrier universes.
- `eulerPolynomial_of_shortExact`: multiplicativity along a short exact
  sequence whose middle term is continuous. By the Library's
  `localWeilContinuity`, a continuous representation has finite inertia
  image, so `eulerPolynomial_invariants_of_shortExact` applies.
- `lFactorClass`, `lFactorClass_isExactAdditive`: the L-factor on isomorphism
  classes of continuous representations, as an element of
  `Additive (RatFunc ℂ)ˣ`, and its additivity on short exact sequences.
- `lFactorHom F` (the selected declaration): the ℤ-linear map from
  `ExactGrothendieckGroup.Continuous (localWeilGroup F)` to
  `Additive (RatFunc ℂ)ˣ` obtained from the universal property `lift`. So the
  L-factor of a sum of virtual classes is the product of the L-factors, and an
  integer multiple becomes an integer power. `lFactorHom_ofRepresentation`
  gives its value `lFactorUnit F A` on the class of a continuous `A`.
- `characterEulerPolynomial F χ`: `1 - χ(Fr) X` if the continuous character
  `χ` of `W_F` is trivial on inertia, and `1` otherwise.
  `eulerPolynomial_characterLine` shows that this is the Euler polynomial of
  the character line. The proof uses the Library's scalar-character Euler
  polynomial results for the unramified and ramified cases.
- `characterLFactor F χ`: `characterEulerPolynomial F χ` inverted in
  `RatFunc ℂ`; `coe_lFactorUnit_characterLine` and `lFactorHom_characterClass`
  identify it as the value of the L-factor on `characterClass χ`.
- `lFactorHom_continuousInduceAlong`: on the virtual class induced along
  `extensionWeilMap F E g : W_E → W_F` from a continuous representation `A`
  of `W_E`, the homomorphism takes the value `lFactorUnit F` of the induced
  representation `induceAlong (extensionWeilMap F E g) A`.
- `eulerPolynomial_induceAlong_characterLine`: for a continuous character `χ`
  of `W_E`, the Euler polynomial over `F` of the representation induced from
  `χ` is `P_χ(X^f)`, where `P_χ = characterEulerPolynomial E χ` and `f` is
  the residue degree `extensionResidueDegree F E g`. It is the first conclusion
  of the Library's `eulerFactorInduction`, applied to the character line in
  carrier universe `u` and to the Frobenius lifts of degree one; the character
  line is moved to that universe by `induceAlongEquivOfEquiv`.
- `inducedLFactor F E g χ`: `P_χ(X^f)` inverted in `RatFunc ℂ`;
  `coe_lFactorUnit_induceAlong_characterLine` and
  `lFactorHom_continuousInduceAlong_characterClass` identify it as the value
  of the L-factor on the induced character class.

## Arithmetic pair L-factors

- `arithmeticPairLFactor_zeroMonodromy`: for local Weil representations `V`,
  `W` of `F` and any representation `T` (any carrier universe) with an
  equivalence `T ≃ V ⊗ W`, the published `Correspondence.arithmeticPairLFactor`
  of the zero-monodromy pairs of `V` and `W` (with the norm character as
  twisting character) is `lFactorUnit F T`. The proof uses
  `pairLFactorClass_classOf`, the definition of the pair L-factor as the
  rational L-factor of the tensor product, `tensorZeroMonodromyEquiv` and
  `eulerPolynomial_zeroMonodromy`.
- `arithmeticPairLFactor_eq_of_virtualIdentity`: let `T` be continuous with
  `T ≃ V ⊗ W` and carrier universe `max u w`. Let `J` be a finite type, with
  p-adic fields `E j`, embeddings `g j : F → E j`, continuous characters
  `α j`, `β j` of `W_{E j}`, integers `n j`, a continuous character `α₀` of
  `W_F` and an integer `d`. Suppose that in the continuous exact virtual group
  of `W_F`
  `[T] = d • [α₀] + Σ_j n_j • Ind_{g_j}([α_j] - [β_j])`,
  where `Ind_{g_j}` is `continuousInduceAlong` along `extensionWeilMap F (E j) (g j)`.
  The class of `α₀` uses carrier universe `max u w`, and those of `α_j`, `β_j`
  use carrier universe `w`. Then the arithmetic pair L-factor of the
  zero-monodromy pairs of `V` and `W` equals
  `characterLFactor F α₀ ^ d * Π_j (inducedLFactor F (E j) (g j) (α j) /
  inducedLFactor F (E j) (g j) (β j)) ^ n_j`.
  The proof applies `lFactorHom` to the identity and evaluates each term with
  the lemmas above.
- `arithmeticPairLFactor_dual_eq_of_virtualIdentity`: assume the same
  identity, and let `Vd`, `Wd` be representations with equivalences
  `Vd ≃ V^∨` and `Wd ≃ W^∨`. Then the arithmetic pair L-factor of the
  zero-monodromy pairs of `Vd` and `Wd` is the same expression with `α₀`,
  `α j`, `β j` replaced by their inverse characters. The proof takes
  contragredients of the identity: the Library's
  `continuousDual_ofRepresentation` and `continuousDual_characterClass`, with
  `continuousDual_continuousInduceAlong` above. It then applies the previous
  theorem to `T^∨`, which is continuous and, by `dualEquiv`,
  `tensorDualEquiv` and `tensorEquiv`, equivalent to `Vd ⊗ Wd`.

No semisimplicity is assumed: everything holds at the level of the continuous
exact virtual group. Epsilon factors are not treated here.
