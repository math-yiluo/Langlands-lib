# Categorical exactness of the actual nondegenerate functors

Authors: Workers 6 and 490. Worker 6 supplied the shared statement draft;
Worker 490 checked its source correspondence and published prerequisites,
prepared this explanation, and checked the complete proposition.

`Langlands.Algebra.NondegenerateModuleExactnessStatement.{uA,uM}` is a
closed proposition definition. It universally quantifies over `A : Type uA`,
`[NonUnitalRing A]`, and `hA : IsIdempotented A`. The latter is the published
finite local-unit condition: every finite set of ring elements lies in a
common idempotent corner. The module carrier universe `uM` is independent
of the ring universe `uA`.

The body is exactly the following four assertions, in this order:

1. `(nondegenerateInclusion.{uA,uM} A).PreservesHomology`.
2. `(nondegeneratePartFunctor.{uA,uM} hA).PreservesHomology`.
3. For every `S : ShortComplex (NondegenerateModuleCat.{uA,uM} A)`,
   `(S.map (nondegenerateInclusion A)).Exact ↔ S.Exact`.
4. For every `S : ShortComplex (NonUnitalModuleCat.{uA,uM} A)`,
   `S.Exact → (S.map (nondegeneratePartFunctor hA)).Exact`.

In the pinned Mathlib, `Functor.PreservesHomology` is the Prop-valued
certificate that the functor preserves the limit and colimit of every
parallel pair consisting of an arrow and the zero arrow. These are kernel
and cokernel preservation. The certificate does not itself assume global
kernel or cokernel existence. `ShortComplex` consists of two composable
arrows whose composite is zero. Its categorical predicate `Exact` asserts
that there exists homology data whose left homology object is zero. Thus
the third clause asserts both preservation and reflection of exactness by
the inclusion, and the fourth asserts preservation of exactness by taking
the nondegenerate part. The complete body contains no additional clauses
or hypotheses.

The imported `Langlands.Algebra.NondegenerateModuleAdditive` uses the
published `NonUnitalModuleCat.preadditive`, with pointwise addition on the
original additive intertwining maps. Its full subcategory
`NondegenerateModuleCat` inherits these Hom groups through
`Preadditive.fullSubcategory (nondegenerateProperty A)`. The inclusion is
the actual full-subcategory inclusion. The part functor takes an original
module to its actual stable additive subgroup of vectors fixed by some
ring idempotent; its map on arrows is the original intertwiner restricted
to these subgroups. The imported additive instances supply preservation of
zero morphisms required to form the mapped short complexes and the
homology-preservation predicates. No alternative action, category,
functor, or preadditive structure is introduced here.

All preservation certificates occur as conclusions. There is no abelian,
closure, adjunction, or exactness certificate among the inputs. Original
actions satisfy additivity and associativity without a unit-action law,
even when the ring has an identity. The statement therefore covers zero
actions, zero rings, and trivial carriers. It assumes no nontriviality,
field, commutativity, dimension, or finiteness condition. The Lean file
checks the entire unfolded proposition by `rfl` at arbitrary independent
`uA,uM` and at both unequal pairs `(0,1)` and `(1,0)`, and assigns the named
definition to `Prop`.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original module conventions are printed pp.5–6/PDF11–12. I.1.2, printed
p.7/PDF13, defines the nondegenerate full subcategory and largest
nondegenerate part and asserts submodule/quotient closure and abelianness.
Printed p.8/PDF14 states exactness of the part functor and proves the
range-kernel equality for the actual restricted arrows: an idempotent
fixing a kernel vector adjusts any preimage into the source part. A.VI.2,
printed p.262/PDF268, gives the categorical image/kernel exactness
framework and the Hom-addition property.

The kernel/cokernel formulation and reflection of exactness by the fully
faithful inclusion are internal categorical formulations motivated by
these passages. Inclusion exactness is a consequence to be proved from
the concrete closure constructions, rather than an explicit assertion on
PDF13. The abelianness route must also supply zero and finite-product
closure: the unrestricted abelian-subcategory criterion in A.VI.1 is
insufficient, as explained in
[the source-discrepancy note](../../notes/renard/appendix-a-corrections.md).
This proposition assumes no such criterion. These derived formulations
explain its provenance; this file supplies the statement, not its proof.

The categorical proof, original range-kernel preservation proof, ambient
categorical exactness comparisons, nondegenerate abelianness, completion,
other adjunctions, and scalar comparisons retain their separate obligations.
