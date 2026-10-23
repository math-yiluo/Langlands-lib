# Ring-map naturality of affine rational and adelic multiplicative comparisons

Fix a scheme `S`, commutative rings `R` and `R'` as objects of `CommRingCat`,
a structure map `f : Spec R ⟶ S`, and a ring morphism `r : R ⟶ R'`.
The induced test-scheme arrow is the actual `Tate.affineTestMorphism f r`
from `Over.mk (Spec.map r ≫ f)` to `Over.mk f`.

## Provenance and rational restriction

This internal unit extends `MultiplicativeAffineTestScheme` using
`RationalTestScheme`, `MultiplicativeRationalAffine` and the existing
prime-adic rational comparison. No new original-literature assertion is
used. All root modules and maps are the existing actual roots-of-unity
limits and their scalar extensions.

For any commutative group object `G` over `S` and selection predicate `P`,
`Tate.affineRationalTestRestrict G f r P` abbreviates the existing
`rationalTestRestrict` along this affine arrow. Its source and target are
the published rational Tate modules, obtained by tensoring the corresponding
integral modules over `ℤ` with `ℚ`. In particular it applies to an actual
abelian scheme through `A.toGrp`.

## Selected rational and finite-adelic squares

`affineRationalEquiv_testRestrict` proves

```
affineRationalEquiv (Spec.map r ≫ f) P
    (Tate.affineRationalTestRestrict (Gm S).toGrp f r P x)
  = TateTwist.Divisibility.rationalMap P r.hom
      (affineRationalEquiv f P x).
```

The proof uses induction on the rational tensor product. On pure tensors,
the assertion is the integral affine naturality law; the additive case
follows from linearity. The inverse square
`affineRationalEquiv_symm_testRestrict` follows by applying the injective
target comparison and its inverse identities. Both laws cover the full
system and the selection of orders coprime to any natural modulus.

The two `affineFiniteAdeleEquiv` laws express these same identities for the
published finite-adelic linear bundles. The hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison` remains explicit and
is used for both comparison maps, the test-scheme restriction, and the
ring-induced twist map. The proofs reuse the rational equalities because
the underlying functions of these bundles are unchanged.

## Away finite-adelic squares

The forward and inverse `affinePrimeToFiniteAdeleEquiv` laws use the
selection `Nat.Coprime · m` and the explicit hypothesis
`hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`.
The full comparison `h` is an implicit parameter of that hypothesis.
The same coupled witness is used for every bundle in each square. These
are specializations of the rational selected squares, and do not prove
the assumed scalar-comparison propositions. The natural modulus `m` need
not be prime.

## Rational prime-adic squares

For a prime natural number `p`, `affinePrimeRationalEquiv_testRestrict`
proves the corresponding square between the actual `Gm` module
`ℚ_[p] ⊗[ℤ_[p]] Tate.PrimeAdic.Integral` and the rational root twist over
`R` and `R'`. The proof expresses the integral affine prime-adic square as
equality of composed linear maps, applies scalar extension over `ℤ_[p]`,
and evaluates the result. The inverse square follows by injectivity.

## Scope

These are algebraic restriction laws for affine test schemes over the
fixed base `S`. No rational topology or continuity, base-scheme change,
geometric path transport, monodromy trivialization, rank, finite étaleness,
Weil pairing or completion of the parent PEL task is asserted. No roots of
unity or basis for a twist are chosen.
