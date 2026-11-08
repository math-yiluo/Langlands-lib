# Scalar comparisons of the original Harris torsion systems

This internal construction reduces the scalar comparisons of
`HarrisLatticeCommensurability` on the existing `HarrisReduction` torsion systems.
It uses the original lattice actions, quotient modules and exponent transitions.
It does not assume that reduction preserves injectivity.

The parameters are the rational algebra with involution, number field `L`,
finite-dimensional algebraic coefficient representation `ρ`, rational finite
place `p`, and two compact open levels `U,V` of the original finite-adelic group.
Write `R = HarrisCoefficientIntegers L p`, `Λ_U = harrisLattice ρ p U`,
`I = harrisCoefficientScalarIdeal L p m`, and
`r = harrisLatticeComparisonScalar ρ p U V`. The scalar `r` is the same ordered
choice in both directions. No symmetry or level naturality of this choice is
asserted.

For any subgroup `T` contained in both level groups,
`harrisRestrictedTorsionSystem` is the original functor
`harrisTorsionSystem`, followed by action restriction along the given inclusion.
Its term at `n` has underlying module `Λ_U / I^n Λ_U`; all its transitions and
its `T`-action are the original ones. There is no compactness or openness
requirement on `T`.

`harrisTorsionSystemScaledComparison` and
`harrisTorsionSystemScaledComparisonBack` are natural transformations between
these original restricted systems. Their components apply the existing
`powerReduction` functor to the full-lattice equivariant scalar maps. The
representative formulas send `[x]` to the class of the corresponding original
full-lattice scalar map of `x`. Naturality of the quotient transition proves
compatibility with every exponent transition; the two named transition laws
also display these equations explicitly.

The two composites are `r*r` times the identity natural transformation of
the respective original restricted system. The proof uses extensionality of
natural transformations, action morphisms and module maps, then the surjectivity
of the quotient presentation. On a representative it is the image, under the
quotient map, of the already proved full-lattice scalar-square equation.
These are equations over the original ring `R`, including exponent zero and
every natural number `m`; no nonzero-modulus premise is required.

When `V` is contained in `U`, `harrisRestrictedTorsionSystemInclusion` is
literally the existing `harrisTorsionSystemInclusion` whiskered with restriction
from `V` to `T`. Its source and target are the original systems at `V,U`.
The representative formula retains the original ambient lattice inclusion.
Three laws follow by quotient representatives from their full-lattice versions:
the reverse comparison equals `r` times this unchanged inclusion, the forward
comparison followed by the inclusion equals `r` times the identity at `U`,
and the inclusion followed by the forward comparison equals `r` times the
identity at `V`.

This is an internal functorial deduction from the imported lattice comparisons
and quotient constructions, with no new external-source claim. It constructs
integral torsion-system maps and their intrinsic laws. It asserts neither
injectivity nor invertibility of the reduced maps, rational adic or associated
sheaf independence, nor Hecke compatibility. The geometric existence,
canonical-model and remaining host-task obligations are unchanged.
