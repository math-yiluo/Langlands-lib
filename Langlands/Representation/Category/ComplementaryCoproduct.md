# Actual coproduct of complementary invariant subspaces

Worker 491 constructs the coproduct universal property of supplied complementary
invariant subspaces of a smooth representation. This is an internal algebraic
construction from the existing actual subrepresentation objects, Mathlib's
`LinearMap.ofIsCompl`, and the existing A.IX `IsCoproductOfComponents` predicate.
It does not assert that invariant complements exist.

For a commutative ring `R`, a group with any topology, and a smooth `R`-linear
representation `A`, `complementaryComponents A S Q` places the actual
subrepresentation on `S` at `true` and the actual subrepresentation on `Q` at
`false`. `complementaryCofan` has ambient object `A` and the literal inclusion
morphisms. The ring, group and representation carrier universes are independent.
Neither local compactness nor a chain condition is required.

If the underlying submodules of `S` and `Q` are complementary,
`complementaryDesc` extends a pair of smooth equivariant maps by the linear map
that adds their values on the unique decomposition of an ambient vector.
Invariance of both subspaces and equivariance of the two maps prove that the
extension is equivariant. The two restriction laws are the left and right
restriction identities of `LinearMap.ofIsCompl`.

`complementaryCofanIsColimit` uses this extension as its descent morphism. The
restriction laws prove the cofan equations; decomposing every ambient vector
as a sum proves uniqueness. `isCoproductOfComponents_of_isCompl` then supplies
the exact existing A.IX predicate when the two actual subrepresentations satisfy
the given Bool-indexed object properties. This does not assume that the category
has coproducts of all families of any index size.

The application motivating this unit is the first decomposition in Renard
VI.3.5 (French edition dated 9 July 2026, printed pp.146–147 / PDF pp.152–153),
whose categorical convention is A.IX (printed p.268 / PDF p.274). The source's
existence of the relevant invariant summands, compact-restriction comparisons
and full whole-category decomposition remain separate proof obligations. This
module does not change the published statement or any imported pair, and its
implemented proof is the direct linear universal-property argument described
above. It also differs from `idempotentCofanIsColimit`, which starts with an
idempotent and constructs its kernel and range; here the supplied invariant
subspaces and their literal inclusions are retained.
