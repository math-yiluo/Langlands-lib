# Degree-one vanishing from prime-index normal sections

Author: Worker 263. The exact form of the hypothesis follows the interface
of Worker 58's generic proof draft for the parent idele-class task.

`Langlands.Cohomology.PrimeSectionH1Vanishing` is a proposition
universally quantifying a commutative ring `k : Type u`, a finite group
`G : Type u`, and a representation `A : Rep.{u} k G`, for an arbitrary
common universe `u`. Its hypothesis is: for every subgroup `H` of `G`
and every normal subgroup `N` of `H` whose index in `H` is prime,

`H¹(H/N, A^N) = 0`.

Its conclusion is `H¹(G, A) = 0`. The conclusion is not an assumption.

## Lean objects

All cohomology objects are Mathlib's actual ordinary group cohomology,
imported from
`Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality`.

- Finiteness of `G` is the instance binder `[Finite G]`.
- `N : Subgroup H` is a subgroup of the subgroup `H`, regarded as a group.
  Normality in `H` is the instance binder `[N.Normal]`.
  The index condition is `N.index.Prime`, that is,
  `Nat.Prime (Subgroup.index N)`, the index of `N` in `H`. This is
  equivalently the condition that `H ⧸ N` has prime order; the quotient
  is then cyclic of prime order.
- `Rep.res H.subtype A` is the restriction of `A` along the inclusion
  homomorphism `H.subtype : H →* G`.
- `(Rep.res H.subtype A).quotientToInvariants N` is Mathlib's
  representation of `H ⧸ N` on the `N`-invariants of that restricted
  representation.
- Vanishing is expressed as `Subsingleton (groupCohomology _ 1)`. Each
  cohomology module contains zero, so this is equivalent to every
  degree-one class being zero.

No finiteness hypothesis is placed on `k`, on `A`, or on any cohomology
module, and no hypothesis on the characteristic of `k`, triviality of the
action, or topology is imposed. The hypothesis ranges over all subgroups
`H` of `G`, not only normal ones, and over all prime-index normal
subgroups of each `H`. It is a hypothesis on these quotient sections only;
the proposition does not claim that restriction to subgroups of prime
order detects `H¹`.

## Source correspondence and provenance

This is a derived abstraction of Emil Artin and John Tate,
*Class Field Theory*, AMS Chelsea Publishing, 2009, Chapter XIV,
section 2, Lemma 1 and the Remark following it, printed pages 147–148
(PDF pages 156–157). Registered source
`artin-tate-2009-class-field-theory`, retained at
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
Worker 263 read these pages. No project errata entry for this source was
present when checked.

Artin and Tate work in a formation: layers `L/F` of a tower of fields with
Galois group `G_{L/F}` acting on a module, and `H^r(L/F)` the cohomology of
that layer. Lemma 1 says that if inflation–restriction is exact in degree
`r`, then the divisibility "order of `H^r(L/F)` divides `[L : F]^ν`" holds
for all normal layers once it holds for all cyclic layers of prime degree. The
Remark specializes to `r = 1` and `ν = 0`, where inflation–restriction is
always exact: their Axiom I′ (`H¹(K/F) = 0` for every cyclic layer `K/F`
of prime degree) implies Axiom I (`H¹(K/F) = 0` for every normal layer).

The translation to a single finite group is as follows. Take `G` to be
the Galois group of a normal layer `L/F` and `A` its coefficient module.
An intermediate field `E` corresponds to a subgroup `H = G_{L/E}`, and
`E ⊆ K ⊆ L` with `K/E` normal of prime degree corresponds to a normal
subgroup `N = G_{L/K}` of `H` of prime index. In the formation,
`H¹(K/E)` is the cohomology of `G_{K/E} ≅ H/N` with coefficients in the
`G_{L/K}`-invariant part of the module. That is
`(Rep.res H.subtype A).quotientToInvariants N` here. Thus the hypothesis
is Axiom I′ for the layers of the tower inside `L/F`. The conclusion is
the `L/F` instance of Axiom I. The proof in the source only passes to
layers inside `L/F`, that is, to quotients `H/N'` of subgroups `H` of
`G_{L/F}` by normal subgroups `N'` of `H` with their invariant
coefficients, and to Sylow subgroups. So this group-theoretic form
isolates that reduction.

This proposition does not assert any arithmetic hypothesis. It does not
assert that a particular formation satisfies Axiom I′, nor does it compare
fixed-field coefficient modules with invariant submodules. Those
comparisons are separate obligations. Artin and Tate's modules are
abelian groups with a group action. The commutative-ring parameter `k`
adds scalar structure only: forgetting scalars gives such a module with
the same inhomogeneous cochains, so a `k`-linear cohomology module is a
subsingleton exactly when the underlying abelian group is trivial.

The source proof inducts on the degree of the layer. For a prime-power
layer it uses a proper nontrivial normal subgroup and the
inflation–restriction sequence. Otherwise it uses injectivity of
restriction to Sylow subgroups on primary parts. A proof in Lean may
follow a different route. This file defines the proposition target only;
its proof is a separate task.
