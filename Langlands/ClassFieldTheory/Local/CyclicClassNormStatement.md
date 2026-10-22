# Positive carry classes under the cyclic norm comparison

Author: Worker 80.

`CyclicClassNormNormalization.{u,v}` states that the published cyclic
cohomology comparison sends the positive carry-cocycle class defined by a
base-field unit to that unit's class in the actual field norm quotient:

```
cyclicH2NormEquiv K L σ hσ (cyclicClass K L χ.toMonoidHom a)
  = Additive.ofMul (normQuotientProjection K L a).
```

Here `K : Type u` and `L : Type v` have independent universes. The extension
is finite Galois, `n` is a nonzero natural number, and `χ` is a group
isomorphism from `Gal(L/K)` to `Multiplicative (ZMod n)`. The automorphism
`σ` is supplied with the generator certificate required by the existing
comparison. The additional equality `χ σ = Multiplicative.ofAdd 1`
aligns this generator with the positive cyclic coordinate. In particular,
the isomorphism `χ` prevents replacing the cyclic group by a proper
quotient. The statement includes the trivial cyclic group when `n = 1`.

The source is ordinary degree-two cohomology of the actual action of
`Gal(L/K)` on `Lˣ`, written additively over the lifted integers
`IntegerScalars.{v}`. The target is `Additive` of the existing quotient
`Kˣ / normSubgroup K L`; this subgroup is the image of the determinant
field norm on units. No group, field, or cohomology carrier is replaced.

For `r(g) = (χ g).toAdd.val`, the class on the left is represented by
the included base unit raised to
`floor((r(g) + r(h)) / n)`. This is the positive carry convention:
the integer carry is the coboundary of the rational lift `r(g)/n`.
The comparison on the left is exactly `cyclicH2NormEquiv` from
`CyclicNorm`, including its use of Mathlib's cyclic-resolution
comparison, followed by descent of invariant units and quotient by norms.
The conclusion specifies its value on these actual carry classes;
it does not choose a new comparison to make the formula hold.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, Springer GTM 67 (1979), Chapter VIII, section 4,
Proposition 6 and its corollary and following remark, printed pages
132–133 / PDF pages 138–139. Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 80 read both original pages. No current project errata entry was
present when checked.

Serre uses `D = σ - 1` and the group norm `N`. His positive-even
comparison identifies cohomology with `A^G / NA`. The remark describes
the inverse comparison in degree two as multiplication by the boundary
of the character taking `σ` to `1/n` in `ℚ/ℤ`. For the fixed unit obtained
from `a`, this boundary is precisely the positive carry cocycle:
its rational lift has differential
`r(h)/n - r(gh)/n + r(g)/n`. Descent of that fixed unit gives `a`,
and the group norm descends to the determinant field norm, as proved
in the imported construction.

This target specializes the source's generator-dependent comparison to
the existing unit representation and norm quotient. Identifying
Mathlib's particular resolution comparison with this explicit carry
cocycle is a proof obligation of the target. The statement does not
assume this identification, an invariant map, or a local class formation.
It requires no topology, valuation, unramifiedness, or local-field
hypothesis. It is an algebraic normalization prerequisite; it supplies
neither a proof nor the local H² invariant-existence theorem.
