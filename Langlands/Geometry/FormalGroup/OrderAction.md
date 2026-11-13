# Actions of orders on finite-coordinate formal modules

Let `O` be a commutative ring, `A` a possibly noncommutative `O`-algebra,
and `R` a commutative `O`-algebra. For a finite-coordinate formal
`O`-module `M`, `OrderAction A M` is a unital ring homomorphism from `A`
to the actual ring of `O`-linear formal endomorphisms of `M`. Its
`extends_scalars` equality requires the restriction along `O → A` to
be the given formal scalar action of `M`.

The induced `A`-module structure on `OrderAction.Point` evaluates these
formal endomorphisms on substitutable tuples of power series. Restriction
to `O` agrees with the original scalar action, as `scalar_point` proves.
For points with no formal variables, the underlying tuples are nilpotent
coordinate tuples, as in `ModuleLaw.algebraPointEquiv` after coefficient
extension. No abstract module of points is supplied as extra data.

`map` extends every formal endomorphism along an `O`-algebra map of
coefficient rings. `mapPoints` is linear over the whole order `A`.
`twist` precomposes the action with an `O`-algebra automorphism of `A`.
The scalar restriction condition is preserved in both constructions.

`homSubmodule` is the actual `O`-submodule of formal `O`-linear maps
commuting with all order endomorphisms. Its elements form `OrderAction.Hom`;
they evaluate to `A`-linear maps. Identity, composition and coefficient
extension are constructed from the corresponding actual formal maps.
Coefficient extension preserves identities and composition.
`OrderAction.Iso` records mutually inverse such maps and yields an
`A`-linear equivalence of point modules. Coefficient extension preserves
these isomorphisms. `toModuleIso` forgets the order action.

The proofs use ring-homomorphism laws for the formal action, the existing
evaluation identities, and compatibility of formal substitution with
coefficient maps. Closure of equivariant homomorphisms under addition
and `O`-scalars follows from the bilinearity of formal composition.

The source definition is Drinfeld, *Coverings of p-adic symmetric regions*
(1976), §2 A, printed p.109, the Definition beginning “A formal O_D
module”. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
Taking `A = O_D` gives the action in that definition, within the existing
finite-coordinate scope. The extension to arbitrary `O`-algebras `A`,
its point API, and coefficient extension are derived infrastructure.

This module does not impose the special tangent condition, dimension,
height, or division-algebra hypotheses on `A`. It does not yet construct
locally glued formal groups, Drinfeld's functor `G`, or a representing
formal scheme. Those remain separate obligations of Task 5556.
