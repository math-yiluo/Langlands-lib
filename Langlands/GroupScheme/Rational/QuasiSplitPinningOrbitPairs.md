# Simple-root orbits of Galois-compatible pinnings

This module is an internal prerequisite for the quasi-split Steinberg quotient
task. It shows that the Galois action on simple roots constructed in
`Rational/QuasiSplitCompatiblePinning` satisfies the hypothesis
`IsPairingCompatible` of `Langlands/LinearAlgebra/RootDatumOrbitPairs`. As a
consequence, its orbits are orthogonal unless some orbit contains an `A₂` pair.
Orthogonal orbits are the premise `OrthogonalSimpleOrbits` of the published
orbit-image descent of the canonical Steinberg product.

Throughout, `k` and `K` are arbitrary fields in one universe `u` with an
algebra `k → K`. `G/k` has affine structure morphism. Write `G_K`, `T_K` and
`i_K` for the canonical base changes along `algebraBaseMap k K` of `G`, a
torus `T/k` and an inclusion `i : T → G`. No perfectness, characteristic or
infinitude assumption is made. The structure `PairingCompatiblePinningData`,
the theorem `IsQuasiSplit.exists_pairingCompatiblePinningData` and the orbit
dichotomy do not assume that `G` is locally of finite type. All other
declarations do; the quasi-split theorem derives it from smoothness.

## Galois permutations preserve the pairing

`IsRootDatumOf.galoisRootIndexEquiv_pairing` assumes that `G` is locally of
finite type, `T_K` is split (`hT`), `i_K` is a closed immersion (`hi`), and
`P` is a root datum of `i_K` (`hP`). For every `σ : K ≃ₐ[k] K` and root
indices `a c`, it states

`P.pairing (galoisRootIndexEquiv σ a) (galoisRootIndexEquiv σ c) = P.pairing a c`.

Here `IsRootDatumOf.galoisRootIndexEquiv` is the published ordinary Galois
permutation of the root indices, characterized by ordinary transport of the
actual roots. The proof applies Mathlib's `RootPairing.Hom.pairing` to the
published root-datum automorphism
`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k K i hT hi hP σ`. The
index permutation of that automorphism is `galoisRootIndexEquiv σ` by
definition. Its construction proves the coroot transport, using finiteness of
the Weyl image of a closed split torus.

## The constructed action is pairing-compatible

The following assumptions are those of the section `OfRegular` of
`QuasiSplitCompatiblePinning`:

- a finite type `J`;
- a reduced root datum `P` of `i_K` with index type `J`;
- a ground-field cocharacter `ν₀` whose base change pairs nonzero with every
  root (`hν`).

`IsRootDatumOf.descendedRegularCocharacterSimpleAction_isPairingCompatible`
assumes in addition `hT` and `hi` as above. It proves `IsPairingCompatible`
for the published base `IsRootDatumOf.regularCocharacterBase` and the
published descended action
`IsRootDatumOf.descendedRegularCocharacterSimpleAction`. For each `σ` the
witness is `galoisRootIndexEquiv σ`. The action on a simple root is, by
definition, its value under this permutation.

`GaloisCompatiblePinningData.ofRegularCocharacter_isPairingCompatible` assumes
`K/k` finite and the hypotheses `hG`, `hT`, `hi` of `ofRegularCocharacter`.
Here `hi` is maximality of the torus `i_K`, whose closed-subgroup part
`hi.2.1` is the closed-immersion premise. The theorem states that the data
`ofRegularCocharacter i hP ν₀ hν hG hT hi` has a pairing-compatible action. The
pinning of this data has base `regularCocharacterBase` and root datum `P`, and
its action is the descended action, so the previous theorem applies.

## Data with a pairing-compatible action

`PairingCompatiblePinningData k K G` extends `GaloisCompatiblePinningData k K G`
by one field, `isPairingCompatible : IsPairingCompatible pinning.base action`.
The field states that for every `σ : K ≃ₐ[k] K` the action of `σ` on the simple
roots is the restriction of a permutation of all root indices that preserves
the integral pairing.

- `PairingCompatiblePinningData.ofRegularCocharacter` has the hypotheses of
  `GaloisCompatiblePinningData.ofRegularCocharacter`. It is that data together
  with `ofRegularCocharacter_isPairingCompatible`.
- `TorusCentralizerTorusData.nonempty_pairingCompatiblePinningData` has the
  same hypotheses as `nonempty_galoisCompatiblePinningData`: a split torus `A`,
  supplied centralizer data `C`, `G` connected reductive and locally of finite
  type, `K/k` finite, `RootDatumExistenceStatement`, and splitness of the base
  change of `C.torus`. It concludes
  `Nonempty (PairingCompatiblePinningData k K G)`. The proof obtains a reduced
  root datum from `RootDatumExistenceStatement`, using connected reductivity of
  `G_K` and maximality of the base-changed centralizer torus. It then applies
  the previous construction to the regular descended cocharacter
  `C.regularCocharacter hA`.
- `IsQuasiSplit.exists_pairingCompatiblePinningData` assumes only
  `ParabolicDynamicStatement`, `RootDatumExistenceStatement` and
  `IsQuasiSplit G`, besides the affine structure-morphism instance used to form
  the structure. It gives a finite Galois extension `K/k` with
  `Nonempty (PairingCompatiblePinningData k K G)`. The proof follows
  `IsQuasiSplit.exists_galoisCompatiblePinningData`:
  1. Smoothness of `G` gives local finite type.
  2. The published conditional theorem
     `IsQuasiSplit.exists_maximalSplitTorus_with_torusCentralizer`, used with
     the proved `dynamicCentralizerReductive`, gives centralizer data.
  3. The proved `torusFiniteGaloisSplitting` gives a finite Galois splitting
     field, and the previous theorem applies.

The two named statements are explicit premises and are not proved here.

## Orbit dichotomy

`PairingCompatiblePinningData.orthogonalSimpleOrbits_or_exists_pair` takes any
`D : PairingCompatiblePinningData k K G'`. It concludes one of two
alternatives:

- `D.pinning.OrthogonalSimpleOrbits D.action`;
- there are `σ` and a simple root `a` with `D.action σ a ≠ a`, both pairings of
  `a` and `D.action σ a` equal to `-1`, and `D.action σ (D.action σ a) = a`.

If every moved simple root pairs with its image to a value other than `-1`,
`isOrthogonal_of_forall_pairing_ne_neg_one` gives the first alternative.
Otherwise there is `σ, a` with `D.action σ a ≠ a` and pairing `-1`. These
roots are not orthogonal, so `pairing_eq_neg_one_of_not_isOrthogonal` and
`apply_apply_eq_of_not_isOrthogonal` give the second.

## Scope

The module does not decide which alternative holds for a given group. It does
not construct Steinberg's modified products for `A₂` pairs or the canonical
quotient, and it does not prove `ParabolicDynamicStatement` or
`RootDatumExistenceStatement`. All declarations use only the standard axioms.
