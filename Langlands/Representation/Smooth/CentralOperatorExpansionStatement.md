# Uniform finite expansion of central action operators

Worker 345 defines `Langlands.CentralOperatorExpansionStatement.{uG,uA,uV}`
as a closed proposition. This file states the result; it does not prove it.

## Exact statement

Let `G : Type uG` be a topological group, `A : Type uA` an abelian topological
group, and `V : Type uV` a complex vector space. These universes are independent.
Let `ρ : Representation ℂ G V` and `c : A →* Subgroup.center G`, with
`Continuous c` for the subtype topology on the actual center. Assume:

- `IsAdmissible ρ`: every vector is fixed by an open subgroup, and the fixed
  space of every open subgroup is finite dimensional over `ℂ`.
- `Module.Finite (MonoidAlgebra ℂ G) ρ.asModule`: finitely many vectors generate
  `V` under complex linear combinations of their `G`-translates.

Write `S` for the complex subspace of `Module.End ℂ V` spanned by the actual
operators `σ(a) = ρ ((c a : Subgroup.center G) : G)`. There exist a finite set
`X : Finset (A → ℂ)` and an assignment `T : (A → ℂ) → Module.End ℂ V` such that:

1. For every `χ ∈ X`, `χ` is continuous and the functions `a ↦ χ(b * a)`,
   as `b` ranges over `A`, span a finite-dimensional complex subspace of `A → ℂ`.
2. For every `χ ∈ X`, `T χ ∈ S`.
3. For every `a : A`, the equality of endomorphisms is
   `σ(a) = ∑ χ ∈ X, χ(a) • T χ`.

The values of `T` outside `X` are unrestricted. The same `X` and `T` work for
all vectors and all complex linear functionals, since the equation holds before
either is applied. The functions called `χ` need not be multiplicative characters.
The left-translate convention is exactly `χ(b * a)`; using inverses would give
the same translate family because `b` ranges over a group.

There is no topology on `V`, nonzero condition on `V`, finite-dimensionality
assumption on `V`, irreducibility hypothesis, scalar or unitary central character,
assumed finiteness of `S`, or assumed generalized-character decomposition. In the
zero representation, `X` may be empty. Neither `G` nor `A` is required to be
Hausdorff or locally compact. No injectivity or surjectivity of `c` is required.

## Derived mathematical route

The following argument explains the statement's provenance and intended proof;
it is not an implemented Lean proof.

First choose finitely many group-algebra generators `v₁, …, vₘ`. Smoothness gives
an open subgroup `Kᵢ` fixing each `vᵢ`. Every element of `S` commutes with `ρ(g)`
for every `g : G`, because `c` takes values in the actual center and this property
is preserved by complex linear combinations. Thus every `T ∈ S` takes `vᵢ`
into `V^{Kᵢ}`. Evaluation gives a linear map

`S → ∏ᵢ V^{Kᵢ},     T ↦ (T vᵢ)ᵢ`.

This map is injective: a commuting operator vanishing on all generators vanishes
on all their group translates and hence on `V`. Each target factor is finite
dimensional by admissibility, so `S` is finite dimensional. This is a uniform
operator-space conclusion; vectorwise center-finiteness alone does not state it.

Second, choose a finite basis `T₁, …, T_d` of `S` and take the coordinate
functions `χⱼ(a)` of `σ(a)` in that basis. They give the required equality and
each basis operator lies in `S`. These functions are locally constant, hence
continuous: the intersection of the finitely many `Kᵢ` has open preimage `H` in
`A` under the continuous map `a ↦ (c a : G)`. For `h ∈ H`, centrality and
generation imply `σ(h) = id` on all of `V`. Consequently `σ` and its coordinates
are constant on the open cosets of `H`. This argument needs no topology on `V`
or on the endomorphism space.

The space `S` is stable under left multiplication by every `σ(b)`, because
`σ(b) σ(a) = σ(b * a)` and the spanning operators are closed under this
product. For fixed `b`, the matrix of that linear map in the chosen basis
expresses each `a ↦ χⱼ(b * a)` as a linear combination of the finitely many
coordinate functions. Each coordinate therefore has finite-dimensional
translate span. Distinct basis coordinates are distinct functions: a relation
between them vanishing on all `σ(a)` vanishes on their span `S`, and hence on
every basis vector. Thus the indexed family can be represented by the finite
set `X` without losing terms. If `S` is zero, use an empty basis and empty `X`.

Only open fixed spaces and finite intersections are used in this argument;
compactness and separation axioms play no role. The broader topological scope,
the arbitrary center-valued map `c`, and the finite-generator evaluation step
are internal derived content, not a verbatim statement from JPS or Casselman.

## Original sources and scope

- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic Forms on
  GL(3) I*, Annals of Mathematics (2) 109 (1979), 169–212; registered source
  `jps-1979-gl3-i`, SHA-256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
  Retained file:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
  Printed p.181, PDF p.14, defines finite functions just before Proposition 2.2.
  The first paragraph of its proof expands a smooth representation of `Fˣ`
  whose operator algebra is already assumed finite dimensional into finitely
  many finite functions times operators in that algebra. Our statement supplies
  that finiteness from the ambient admissible, finitely generated representation
  and permits a general abelian topological group `A`. It asserts neither the
  proposition's Whittaker expansion nor the paragraph's subsequent assertion
  about spanning by elements with absolute value at most one.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft of 1 May 1995; registered source
  `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
  Retained file:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
  Printed/PDF p.18 gives smoothness, admissibility, group-translate generation,
  and subgroup-finiteness. Proposition 2.1.3 and its proof on printed/PDF p.19
  establish center-finiteness using finite-dimensional fixed spaces stable
  under the center. The source assumes a locally compact Hausdorff group with
  a compact-open subgroup basis. We use its fixed-space argument, not its more
  general closed-subgroup conclusion, and combine it with finite generation
  to obtain uniform operator-space finiteness as explained above.

The originals at these locations were read. No source-specific files named
`notes/errata/jps-1979-gl3-i.md` or
`notes/errata/casselman-1995-admissible-representations.md` were present in the
project or the current Library when this statement was prepared.

## Dependencies and intended uses

The only project import is `Langlands.Representation.Smooth.Definitions`,
which supplies the actual `IsAdmissible` predicate and fixed spaces. Mathlib
supplies representations and their group-algebra modules, the actual subgroup
center and its topology, complex scalars, finite-dimensionality, submodule spans,
and finite sums. Existing Library pairs are unchanged.

`Langlands.Representation.Exponents.CentralStatement` concerns vectorwise
center-finiteness and generalized-character decomposition. It is not imported
or assumed here. Neither is the irreducible scalar-character result in
`Smooth.Schur.Proof`.

A proof of this proposition will apply to scalar matrices in a general linear
group and to one-parameter subgroups of actual product-Levi centers, by supplying
the corresponding continuous center-valued homomorphism. Those applications
must establish the hypotheses for their representations. Full-torus Whittaker
assembly and finite-function product/pullback closure remain separate results.
