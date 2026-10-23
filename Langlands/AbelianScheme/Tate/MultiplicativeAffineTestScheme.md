# Ring-map naturality of the affine integral multiplicative comparisons

Fix a scheme `S`, commutative rings `R` and `R'` as objects of `CommRingCat`,
a structure morphism `f : Spec R ⟶ S`, and a ring morphism `r : R ⟶ R'`.
The new test scheme is `Spec R'` with structure morphism `Spec.map r ≫ f`.

## Provenance and the test morphism

This is an internal construction from the existing actual test-scheme
restriction and affine multiplicative comparisons. Its additional input is
Mathlib's `Scheme.ΓSpecIso_naturality`, the naturality of the canonical
isomorphism from the global sections of `Spec R` to `R`. No new
original-literature assertion is used.

`GroupScheme.Tate.affineTestMorphism f r` is the arrow

```
Over.mk (Spec.map r ≫ f) ⟶ Over.mk f
```

whose underlying scheme map is exactly `Spec.map r`. This uses the actual
contravariant spectrum map and its composite structure morphism; no test
map is supplied independently of `r`.

## Selected, full and away integral squares

For any predicate `P : ℕ → Prop`, `affineIntegralEquiv_testRestrict` proves
that restricting a `Gm` Tate element along this arrow and then applying
the affine comparison equals first applying the affine comparison over
`R` and then mapping the actual root families by `r.hom`:

```
affineIntegralEquiv (Spec.map r ≫ f) P
    (Tate.testRestrict (Gm S).toGrp P (Tate.affineTestMorphism f r) x)
  = TateTwist.Divisibility.map P r.hom (affineIntegralEquiv f P x).
```

The proof first uses the general test-scheme comparison square. The
remaining two composites of root maps agree by functoriality of the root
map and the ring-map equality underlying `Scheme.ΓSpecIso_naturality r`.
Thus the statement compares roots in `R` and `R'` themselves, with the
canonical global-section identifications accounted for.

`affineIntegralEquiv_symm_testRestrict` proves the inverse square by applying
the injective target equivalence and its inverse identities. The selected
result includes the full system by setting `P` constantly true.
`affineFullContinuousLinearEquiv_testRestrict` exposes that case through the
existing continuous full comparison and full residue-linear restriction.
The two `affineAwayContinuousLinearEquiv` laws expose the forward and inverse
squares for orders coprime to any natural modulus `m`, using the actual away
residue-linear maps. They are specializations of the selected identities;
no primality assumption on `m` is needed.

## Prime-adic integral squares

For a prime natural number `p`, `affinePrimeIntegralEquiv_testRestrict`
proves the analogous square with `Tate.PrimeAdic.testRestrict`,
`affinePrimeIntegralEquiv` and `TateTwist.map p r.hom`.
Its proof uses the general prime-adic comparison square and the same
naturality of the canonical global-section isomorphism.
`affinePrimeIntegralEquiv_symm_testRestrict` gives the inverse square by
injectivity. These are identities for the published `ℤ_[p]`-linear maps;
the integral maps retain their previously established continuity.

## Scope

These are fixed-base restriction laws for affine test schemes. The module
does not change the base `S`, assert transport along a geometric path,
trivialize the Tate twist, or prove finite étaleness, rank, a Weil pairing
or completion of the parent PEL task. Rational and adelic naturality are
not asserted here.
