# Fredholm's criterion for local finite type

Module `Langlands.Analysis.Meromorphic.FredholmCriterionStatement` states the
two results of Bernstein–Lapid §3.4 as proposition definitions. It supplies no
proof.

- `FredholmCriterionStatement`: the Lemma (Fredholm's criterion).
- `HilbertFredholmCriterionStatement`: Corollary 3.4.
- `FredholmFiniteTypeStatement`: their conjunction.

They are the tool by which Bernstein–Lapid verify the local finite type
hypothesis of the principle of meromorphic continuation
(`Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement`); the paper
applies Corollary 3.4 on p.219 to obtain local finite type. The predicates
`IsHolomorphicOperatorFamilyOn` and `IsFiniteTypeOn` are those of
`Langlands.Analysis.Meromorphic.AnalyticSystems`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; journal PDF in the
registered folder. §3.4 begins on p.194 with the Lemma (Fredholm's criterion)
and its proof; Corollary 3.4 and the definition of Hilbertian spaces are on
p.195. As throughout §3, `M` is a complex analytic manifold (p.192).

## Common setting

`E` is a finite-dimensional complex normed space and `M` a manifold charted on
`E` with `IsManifold 𝓘(ℂ, E) 1 M`, a complex analytic manifold as in the
principle of meromorphic continuation. No connectedness is assumed, as in the
source. "Near `s₀`" is expressed as: there is an open set `U` containing `s₀`
on which the family is of finite type (`IsFiniteTypeOn 𝓘(ℂ, E) _ U`), which is
Definition (2) of §3.3 on the open submanifold `U`. Four independent universes
are used for `E`, `M`, `B` and `C`.

## Fredholm's criterion

`B` and `C` are complex Banach spaces and `μ : M → B →L[ℂ] C` is a holomorphic
family of operators on `M`. The hypothesis "`μ s₀` is left invertible modulo
compact operators" is: there is an operator `D : C →L[ℂ] B` such that
`D ∘ μ s₀ - id_B` is a compact operator (`IsCompactOperator`). The conclusion
is that the homogeneous system `μ s v = 0` is of finite type near `s₀`: its
solution sets `{v | μ s v = 0}` are contained in the ranges of a holomorphic
family of injective operators `ℂⁿ → B` on an open neighborhood of `s₀`.

## Corollary 3.4

The source states the corollary for Hilbertian spaces, topological vector
spaces isomorphic to a Hilbert space ("we do not care about the inner product
itself, only the topology"). The Lean statement takes `B` and `C` to be
complex Hilbert spaces. Every notion in the corollary (holomorphic operator
family, topological embedding, compact operator, finite type) depends only on
the topology and the linear structure. A Hilbertian space carries the inner
product of any Hilbert space isomorphic to it, so the two formulations are
equivalent.

`μ, ν : M → B →L[ℂ] C` are holomorphic families of operators on `M`. The
source's "strict embedding" `μ s₀` is a topological embedding
(`Topology.IsEmbedding`): injective, with the subspace topology on its image.
`ν s₀` is compact. The conclusion is that the homogeneous system
`μ s v = ν s v` is of finite type near `s₀`. The source's justification is
that a strict embedding of Hilbertian spaces is left invertible, so the
Lemma applies to `μ - ν`.

## Scope

Nothing is asserted about the principle of meromorphic continuation itself,
about Fredholm indices, or about uniform moderate growth spaces and the
system of Bernstein–Lapid §8.
