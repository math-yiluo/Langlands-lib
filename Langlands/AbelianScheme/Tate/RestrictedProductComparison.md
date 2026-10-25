# Normalized rational Tate restricted-product equivalences

This module packages the published full and away restricted-product
comparison proofs as normalized maps, equips the existing restricted
products with rational module structures, and records naturality and
scalar-coordinate laws. Its provenance is internal: the existence input
is the proved `rationalRestrictedProductComparison` and
`rationalAwayRestrictedProductComparison` in
`Langlands.AbelianScheme.Tate.RestrictedProductProof`. It does not assume a
new comparison proposition or re-prove the additive comparison.

## Carriers and hypotheses

The first namespace is `Langlands.GroupScheme.Tate.PrimeComparison`.
Fix `S : Scheme`, a commutative group object `G : Grp (Over S)` with
`[IsCommMonObj G.X]`, and a test scheme `T : Over S`.
The actual full rational Tate module is
`RationalFull G T = ℚ ⊗[ℤ] Full G T`. The away version
`RationalAway G T m` rationalizes the inverse limit over positive
torsion orders coprime to `m`. The local factors are
`PrimeAdic.Rational G T p = ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral G T p`.

The target `RationalRestrictedProduct G T` is the already published
algebraic restricted product over primes, relative to the images of
the integral local Tate modules. `RationalAwayRestrictedProduct G T m`
restricts the indexing primes to `AwayPrime m`, the primes coprime to
`m`. No finiteness, rank, characteristic, or finite-étaleness hypothesis
is used. Every away declaration allows any `m : ℕ`; `m = 1` retains all
primes and `m = 0` retains none.

## Normalized additive equivalences

`rationalRestrictedProductEquiv G T` chooses the equivalence supplied by
the published full comparison theorem. Its `_apply` formula is

\[
  E(x)_p=\operatorname{rationalFullToPrime}_p(x).
\]

The `_symm_apply` formula states that the prime coordinate of `E⁻¹(y)`
is `y_p`. `rationalRestrictedProductEquiv_unique` proves that any
additive equivalence with the displayed coordinate formula equals `E`.
Thus classical choice does not leave freedom in the comparison map.

`rationalAwayRestrictedProductEquiv G T m` is the corresponding away
equivalence. Its `_apply` formula uses `rationalAwayToPrime` at the
retained prime, with its coprimality proof. It has analogous
`_symm_apply` and `_unique` results. The inverse formulas follow by
applying the coordinate formula to an inverse image; uniqueness follows
by extensionality on elements and primes.

Both `_toRational` theorems identify the image of `1 ⊗ x` with the
published `integralToRestrictedProduct` or
`integralToAwayRestrictedProduct` of `x`. The proofs rewrite the
normalized coordinate formulas and use `rationalToPrime_toRational`.

`rationalRestrictedProductEquiv_restrictAway` proves the square

\[
 E_m\bigl(\operatorname{rationalRestrictAway}_m(x)\bigr)
   =\operatorname{restrictedProductRestrict}_m(E(x)).
\]

It is proved coordinatewise from `rationalAwayToPrime_restrictAway`.
`rationalRestrictedProductEquiv_symm_restrictAway` is the inverse
square, obtained by applying injectivity of `E_m`.

## Rational modules and linear equivalences

`restrictedProductRatModule` transports the rational module structure
along the inverse additive equivalence. `awayRestrictedProductRatModule`
does the same for the away carrier. These are definitions for local
instance installation, not new global instances. The existing
coordinatewise additive groups are retained.

The two `_smul_apply` theorems show that these transported actions are
the usual rational actions in every local factor:

\[
 (q\mathbin{\cdot}y)_p=q\mathbin{\cdot}y_p.
\]

The proof expands transport, then uses rational linearity of the
published prime-coordinate map and the inverse coordinate formula.
Consequently, `rationalRestrictedProductLinearEquiv` and
`rationalAwayRestrictedProductLinearEquiv` bundle the same normalized
maps as rational linear equivalences. Their `_apply` formulas identify
them definitionally with the additive maps.

The two `_scalarAction` theorems additionally record compatibility with
the existing rational residue-ring actions. For the full action and
`a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing`, the formula is

\[
 E(a\cdot x)_p
  = \operatorname{ProfiniteIntegerRing.rationalToPadic}_p(a)
      \cdot E(x)_p.
\]

The away formula uses
`a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m` and its
`rationalToPadic` projection at the retained prime. Here `a·x` denotes
the corresponding existing `rationalScalarAction` or
`rationalAwayScalarAction`. Both proofs rewrite the comparison's
coordinate formula and apply the published scalar-coordinate law.
They do not install actions of these larger rings on the target.

## Naturality and the actual abelian-scheme specialization

For an actual homomorphism `f : G ⟶ H`,
`rationalRestrictedProductEquiv_map` proves

\[
 E_H(\operatorname{rationalMap}(f)(x))
   = \operatorname{restrictedProductMap}(f)(E_G(x)).
\]

`rationalAwayRestrictedProductEquiv_map` is the analogous away square.
The proofs use extensionality and the published prime-coordinate
naturality. Their `_symm_map` versions give the inverse squares,
by injectivity of the comparison for `H`.

The namespace `Langlands.AbelianScheme.Tate.PrimeComparison` supplies
both additive equivalences, both rational module definitions and both
linear equivalences for a bundled actual abelian scheme `A`, through
`A.toGrp`. It restates the coordinate formulas, the forward
full-to-away square, and both forward naturality squares for actual
abelian-scheme homomorphisms via `AbelianScheme.groupHom`.
The remaining group-scheme laws apply through these definitions.
At a geometric point `s`, take `T = Over.mk s`; this uses the already
constructed actual torsion sections.

## Scope

The comparison existence theorems are imported proofs about these
actual carriers. This module adds rational linear packaging and the
listed algebraic compatibilities. It introduces no topology on the
restricted products, no homeomorphism, and no finite-adele module
structure on them. It contains no new geometric, monodromy, or
Weil-pairing assertion. The source conventions and the proof of
comparison existence are documented in the imported `Rational`,
`RestrictedProductStatement`, and `RestrictedProductProof` pairs.
