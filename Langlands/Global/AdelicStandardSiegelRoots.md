# Actual Lie roots of the canonical standard Siegel parabolic

Author: Worker 1623.

For any field `k`, a connected reductive affine group `G` locally of finite
type over `k`, a maximal split torus `i : T → G`, and a generic cocharacter
`ν`, this module proves
`relativeRoots (torusToStandardParabolic k G T i ν) = positiveRelativeRoots i ν`.
The affine structure on the canonical parabolic follows from its existing
closed inclusion into `G`. The field and group universe is unrestricted;
no number-field hypothesis or nonempty-root hypothesis is needed.

`standardParabolicPositiveRootsEquiv` gives the corresponding equivalence
of actual root types. Both directions preserve the character itself.
Thus the positive roots used in the adelic Siegel chamber are tied to the
nonzero weights on the actual canonical parabolic's Lie algebra.

The proof uses `standardParabolic_empty_eq_dynamic_of_generic` to view
the canonical `Standard.parabolicHom i ν ∅` as a representative of the
dynamic parabolic of `ν ≫ i`. The published torus-lift composition identity
then permits
`RelativeRoot.relativeRoots_parabolicRepresentative_of_generic` to identify
its roots. That comparison transfers intrinsic Lie weights along the
monomorphic inclusion and uses the exact nonnegative tangent weight span
of the dynamic parabolic; genericity makes these nonnegative roots positive.
The equivalence is the literal identity on the resulting character sets.

Provenance is derived from the Library's canonical representatives, torus
lift, dynamic subgroup comparison and actual Lie-weight comparison.
There is no additional assertion from the literature.
For number fields the equality proves the root-comparison clause of
`IsSiegelAlgebraicSetup` from the stated torus and genericity hypotheses.
The module does not assert existence of the full algebraic setup or of
compatible compact subgroups or adelic Siegel coverage.
