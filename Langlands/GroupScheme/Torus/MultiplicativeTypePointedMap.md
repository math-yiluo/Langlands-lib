# Pointed maps to groups of multiplicative type

Worker 504.

`Langlands.GroupScheme.multiplicativeTypePointedMap` proves
`Langlands.GroupScheme.MultiplicativeTypePointedMapStatement.{u}` for every
universe `u`. Over any field, a scheme morphism `φ` from a smooth connected
group scheme of finite type to a group of multiplicative type that preserves
the identity section is the underlying map of a homomorphism of group schemes.
The conclusion is the equality `f.hom.hom = φ` for the homomorphism `f`.

## Lean proof

The proof applies `multiplicativeTypePointedMap_of_unitsProductDecomposition`
to `unitsProductDecomposition` at universe `u`. The latter factors every
morphism from a product of irreducible varieties over an algebraically closed
field to the multiplicative group into a product of pullbacks from the factors.
Its proof uses Rosenlicht's tensor-unit theorem on affine charts and extends the
factorization to the full product. [Product-unit proof](UnitsProductDecomposition.md)

The reduction applies that factorization to `φ ∘ m` in the multiplicative-group
case. Evaluation along the two identity axes and at the pair of identities
gives the multiplication law on every test scheme. Coordinate characters
then detect this law for diagonalizable targets. The source remains smooth,
quasi-compact and connected under the field extensions used in the reduction.
Faithful pullback reflects the group-law equations first from an algebraic
closure to the splitting field, then from the splitting field to the original
field. The reduction constructs the required `f` with underlying map `φ`.
[Pointed-map reduction proof](MultiplicativeTypePointedMapReduction.md)

## Source

James S. Milne, *Algebraic Groups* (2017), Proposition 12.49 and its proof,
printed page 247 (PDF page 263), using Proposition 12.48 on printed pages
246–247 (PDF pages 262–263). The registered source is
`milne-2017-algebraic-groups`.
