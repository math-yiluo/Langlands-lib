# Recursive coordinates on the left-unipotent quotient

This module is an internal derived construction of the maps underlying H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions* (1983),
Section 8.3, printed p.449, equation (1), registered source
`jpss-1983-rankin-selberg`. The retained PDF has SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`;
printed p.449 is one-based PDF page 84 (zero-based index 83). The source's
representative is `diag(g,1) z k`. The constructions here isolate its algebra and
topology; they do not formalize the source's integration identity.

All declarations are in `Langlands.RankinSelberg` and work over a field
`F : Type uF`, with no restriction on its universe. The rank parameter `n` ranges
over all natural numbers, including zero. The large rank is `n + 2`, and the
smaller matrix has rank `n + 1`: this is the coordinate map for decomposing
`GL_(n+2)` using `GL_(n+1)`. In particular, `n = 0` uses the actual rank-one
quotient as its lower input.

`recursiveQuotientRepresentative n g a k` is the actual matrix group element
`rankInclusion 1 g * GeneralLinear.scalar a * k`, with multiplication associated
to the left. The scalar is `a : Fˣ`, embedded in rank `n + 2`, and
`k : GeneralLinear (n + 2) F` is arbitrary. The proved
`recursiveQuotientRepresentative_eq_appendIdentity` gives the equal expression
`appendIdentity n 1 g * GeneralLinear.scalar a * k` using the existing map.

The quotient is the published `LeftUnipotentQuotient n F`, namely the quotient
by `QuotientGroup.rightRel (upperUnipotent (n+1) F)`, whose equivalence classes
are left cosets. The proof
`recursiveQuotientRepresentative_unipotent_mul` sends multiplication of `g` by
a lower-rank upper-unipotent element to multiplication of the larger
representative by `corankOneUnipotent u`. This element belongs to the actual
larger upper-unipotent subgroup by the published corank-one construction.
`recursiveQuotientRepresentative_class_invariant` proves equality of the two
larger quotient classes, and `QuotientIntegration.descend` then constructs

```text
recursiveQuotientCoordinates n :
  LeftUnipotentQuotient n F × Fˣ × GeneralLinear (n + 2) F →
    LeftUnipotentQuotient (n + 1) F.
```

The domain product is right associated, with arguments `(q, a, k)`.
`recursiveQuotientCoordinates_mk` evaluates it at an actual class as
`class (rankInclusion 1 g * GeneralLinear.scalar a * k)`.
`recursiveQuotientCoordinates_mk_appendIdentity` gives the same evaluation
with `appendIdentity n 1`. Thus representative independence is proved using
the existing quotient, without choosing representatives.

For every `abv : AbsoluteValue F ℝ`,
`recursiveQuotientRepresentative_det_abs` proves

```text
abv (Matrix.det (recursiveQuotientRepresentative n g a k).val) =
  abv (Matrix.det g.val) * abv (a : F) ^ (n + 2) *
    abv (Matrix.det k.val).
```

The proof combines the published determinant preservation of `rankInclusion`,
the determinant of a scalar matrix, multiplicativity, and preservation of
powers by the absolute value. The last-row helpers
`lastRow_rankInclusion_one_mul` and `lastRow_scalar_mul` prove that the appended
identity coordinate fixes the final row of the following factor, and that
left scalar multiplication scales that row. The combined result
`recursiveQuotientRepresentative_lastRow` is

```text
lastRow (recursiveQuotientRepresentative n g a k) =
  fun j => (a : F) * lastRow k j.
```

These algebraic formulas require only the field structure and impose no
compactness or integrality condition on `k`.

With `[TopologicalSpace F] [IsTopologicalRing F]`,
`continuous_recursiveQuotientRepresentative` proves joint continuity using
the published continuous rank inclusion and scalar homomorphism, followed by
continuous multiplication of matrix units.
`continuous_recursiveQuotientCoordinates` descends that continuity through
`leftQuotient_isOpenQuotientMap` for the smaller group, taking its product with
the identity on the scalar and larger-group factors. The target projection is
also continuous by the same published quotient API. No topological-field
inversion hypothesis is needed beyond the stated hypotheses for these APIs.

This construction selects no measures or normalizations and asserts no
measure pushforward identity, Whittaker square estimate, convergence,
holomorphy, or local factor. Those analytic obligations remain separate.
