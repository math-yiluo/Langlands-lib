# Canonical fixed components in a field tower

This module constructs the isomorphism on full Galois-fixed geometric
components induced by an actual group-scheme isomorphism. It specializes this
construction to the actual pullback-tower isomorphism and proves compatibility
of canonical component extension with a tower of fields.

The content is derived from the published actual point, geometric component
and canonical base-extension constructions. It introduces no external
structural theorem.

## Hypotheses and objects

All fields have the same universe `u`. For the tower construction, `k`, `K`
and `L` are fields with `Algebra k K`, `Algebra K L`, `Algebra k L` and
`IsScalarTower k K L`. The direct `k`-algebra structure on `L` is therefore
compatible with the two successive structures. There is no algebraicity,
separability, perfection or characteristic hypothesis.

`H` is an actual `GroupScheme (Spec (CommRingCat.of k))`, with
`Smooth H.X.hom` and `IsAffineHom H.X.hom`. Write `H_K`, `H_L` and
`(H_K)_L` for `baseChanged k K H`, `baseChanged k L H` and
`baseChanged K L (baseChanged k K H)`.

`GeometricComponents k H` is the existing group of actual connected
components of `H` over the chosen `AlgebraicClosure k`. Its subgroup
`geometricComponentFixedSubgroup k H` consists of components fixed by every
element of `Field.absoluteGaloisGroup k`. In particular, the subgroup is not
restricted to components represented by a base-field section.

## Isomorphisms on the full fixed subgroup

For two smooth affine group schemes `H` and `H'` over the same field `k`,
`geometricComponentFixedIso k e` sends an actual isomorphism `e : H ≅ H'`
to a multiplicative equivalence between their full fixed component groups.
Its forward map is `geometricComponentFixedMap k e.hom`; its inverse is
`geometricComponentFixedMap k e.inv`.

`geometricComponentFixedIso_apply` states the forward value formula.
The inverse identities follow from the existing identity and composition
laws for fixed component maps and the two inverse identities of `e`.

The existing `GaloisPointComparison.towerBaseChangeIso k K L H` is an actual
isomorphism

```text
t : (H_K)_L ≅ H_L.
```

`geometricComponentFixedTowerIso k K L H` is
`geometricComponentFixedIso L t`. Thus it compares two group schemes over
the same field `L`. Its value formula
`geometricComponentFixedTowerIso_val` identifies its underlying geometric
component with `geometricComponentMap L t.hom`.

## Geometric comparison with specified closure embeddings

Let

```text
i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K,
j : AlgebraicClosure K →ₐ[K] AlgebraicClosure L.
```

Restriction of scalars makes `j` a `k`-algebra homomorphism, so the direct
embedding is `a = (j.restrictScalars k).comp i`.
Write `E_i`, `E_j` and `E_a` for the published
`geometricComponentBaseChangeEquivOfEmbedding` with these embeddings and the
corresponding original group scheme. Then
`geometricComponentBaseChangeEquivOfEmbedding_tower` states, for every
`c : GeometricComponents k H`,

```text
geometricComponentMap L t.hom (E_j (E_i c)) = E_a c.
```

The embeddings are inputs to this geometric comparison. The equality holds
on every geometric component.

## Canonical extension through the tower

Write `B_kK`, `B_KL` and `B_kL` for the published
`geometricComponentCanonicalBaseChange` with original groups `H`, `H_K`
and `H`, respectively. Write `T` for
`geometricComponentFixedTowerIso k K L H`.

`geometricComponentCanonicalBaseChange_tower` states, for every
`c : geometricComponentFixedSubgroup k H`,

```text
T (B_KL (B_kK c)) = B_kL c.
```

No embeddings of algebraic closures are supplied to this theorem.
`geometricComponentCanonicalBaseChange_tower_hom` gives the corresponding
equality of homomorphisms:

```text
T.toMonoidHom.comp (B_KL.comp B_kK) = B_kL.
```

## Implemented derivation

The private coefficient calculations use the existing
`coefficientBaseChangeEquiv`. First, projection from the coefficient points
of `H_K` commutes with a coefficient embedding, with restriction of scalars
on the original `H` side. This follows by extensionality of morphisms over
the base and associativity of scheme morphism composition.

Second, the coefficient map of `t.hom` is successive coefficient projection.
The proof first handles an arbitrary morphism satisfying the relevant
projection identity. It then applies this calculation to the published
`towerBaseChangeIso_hom_fst`. This uses the actual pullback projections.

The private `sectionAlong` wrapper makes the existing closure-valued section
comparison explicit in its embedding. Its coefficient formula is precisely
affine-point extension along that embedding. The section tower identity
follows by applying the injective coefficient equivalences, the two
coefficient calculations above, and composition of actual affine-point maps.
Surjectivity of `geometricComponentOfPoint`, together with the existing
point formulas for geometric maps and comparisons, transfers that section
identity to every geometric component.

Finally, choose embeddings `i` and `j` using `IsAlgClosed.lift`. The
published `geometricComponentCanonicalBaseChange_val` computes each
canonical map along any embedding, including the composite `a`. The
geometric tower equality therefore identifies the underlying values of the
two fixed components. Subtype extensionality gives the canonical fixed
tower law; extensionality of homomorphisms gives its homomorphism form.

The equivalence `T` identifies the iterated and direct pullbacks over `L`.
This module does not assert surjectivity of `B_kK`, descent of every fixed
component to a rational point, or an identification with a sheaf quotient.
