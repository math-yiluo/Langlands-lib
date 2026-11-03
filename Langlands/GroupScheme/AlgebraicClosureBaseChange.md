# Comparing chosen algebraic closures after field extension

For arbitrary fields `k K : Type u` with `Algebra k K`, this internal
construction compares two actual successive pullbacks of every group scheme
over `Spec k` to `Spec (AlgebraicClosure K)`. It uses the existing
`GroupScheme.baseChange` throughout.

`algebraicClosureEmbedding k K` chooses a `k`-algebra homomorphism
`AlgebraicClosure k →ₐ[k] AlgebraicClosure K` using Mathlib's
`IsAlgClosed.lift`. Its source is algebraic over `k`, and its target is
algebraically closed. The target's `k`-algebra structure is the existing
scalar-tower structure induced from `k → K → AlgebraicClosure K`.
The homomorphism is injective because its source is a field. No algebraicity
or separability of `K/k` is assumed. The construction chooses one embedding;
it does not assert uniqueness of that choice.

`algebraicClosureBaseMap k K` is the induced map
`Spec (AlgebraicClosure K) → Spec (AlgebraicClosure k)`.
`algebraicClosureBaseMap_comp` proves the commutative square with the two
maps `toAlgebraicClosure` and the original scalar map `Spec K → Spec k`.
The proof is the algebra homomorphism's compatibility with scalars, followed
contravariantly by `Spec`.

`algebraicClosureBaseChangeIso k K` is a natural isomorphism from the functor
that first pulls back to `AlgebraicClosure k` and then along
`algebraicClosureBaseMap k K`, to the functor that first pulls back to `K`
and then to `AlgebraicClosure K`. It composes the inverse of the usual
pullback-composition comparison, the equality of composite base maps just
proved, and the pullback-composition comparison on the other side. The
comparisons are the existing `Over.pullbackComp` lifted to group objects
by `Functor.mapGrpNatIso` and `Functor.mapGrpCompIso`, as in the published
`Langlands.AbelianScheme.Tate.BaseChangeCoherence`.

`algebraicClosureBaseChangeIso_hom_naturality` exposes the naturality
equation for an arbitrary actual homomorphism `i : G ⟶ H`. Thus the
isomorphism compares the base-changed inclusions as well as their source
and target group schemes.

This is derived infrastructure from Mathlib's algebraic-closure embedding
theorem, functoriality of `Spec`, and the Library's actual group-scheme
pullback construction. It uses no new literature assertion. It proves no
preservation of unipotent radicals, Borel maximality, parabolicity, or
connected reductivity; those require their own structural proofs.

Worker 1359 implemented this unit. Workers 445 and 1340 contributed the
existing comparison API, the embedding route, and the naturality requirement.
