# Tower transitivity of the actual idele-class norm

The theorem `Langlands.Global.AdelicFunctoriality.ideleClassNormTower.{u,v,w}`
has exactly the existing proposition `IdeleClassNormTower.{u,v,w}` as its
type. It proves

```text
N_{M/K}(x) = N_{L/K}(N_{M/L}(x))
```

for every actual idele class of `M`, for arbitrary number fields
`K : Type u`, `L : Type v`, and `M : Type w`. The three universe levels
are independent. All three field structures, all three `NumberField`
instances, the three algebras, and `IsScalarTower K L M` are quantified
inside the target in its original order. There are no additional outer
hypotheses. In particular, neither Galois nor abelian extensions are
assumed. Number-field instances supply finite relative dimension.

The proof imports the statement and all existing norm constructions
unchanged. It also exposes `finiteNormComponent_tower`,
`infiniteAdeleNorm_tower`, `adeleNorm_tower`, and `ideleNorm_tower` in the
same namespace. These are identities for the existing maps, not new
choices of norms.

## Implemented proof

The argument extends the already proved principal-norm formula by
continuity in products of local completions. It does not assert that the
diagonal field is dense in the adele ring with its restricted-product
topology.

The private lemma `denseRange_finiteCompletionProduct` first proves weak
approximation in the unrestricted product of all actual finite
completions. For each finite set of height-one primes, the published
`finiteAdicAbv_isNontrivial` and `finiteAdicAbv_isEquiv_iff` show that their
normalized real absolute values are nontrivial and pairwise inequivalent.
Mathlib's `AbsoluteValue.denseRange_algebraMap_pi` gives density in the
finite product of the fields with those absolute values. Applying the
published continuous isometric maps `finiteWithAbsEmbedding` coordinate
by coordinate, using their dense ranges, gives density in the finite
product of actual completions. Finally, `isOpen_pi_iff` reduces every
nonempty open subset of the unrestricted product to such a finite set of
coordinates. Finite weak approximation supplies a diagonal point in that
open set. No uniform approximation over infinitely many primes is used.

At a fixed finite place `p` of `K`, both sides of the desired tower
identity make sense on every family of finite-completion coordinates of
`M`. The direct side is `finiteNormComponent p`. The other side first
applies the existing norm component at each finite place of `L`, then
applies the component at `p`. Both functions are continuous in the
ordinary product topology by `continuous_finiteNormComponent` and the
continuity criterion for maps into a product. Projecting the published
`adeleNorm_principal` identity to a finite coordinate supplies the private
lemma `finiteNormComponent_principal`. On a diagonal element of `M`, the
two functions therefore agree by Mathlib's `Algebra.norm_norm`. The
Hausdorff equalizer argument `DenseRange.equalizer` extends this equality
to the entire product and proves `finiteNormComponent_tower`.

At infinity, `InfiniteAdeleRing.denseRange_algebraMap` gives the requisite
diagonal density directly. The existing infinite-adele norms and their
composition are continuous. Projecting `adeleNorm_principal` to its first
factor and applying `Algebra.norm_norm` proves agreement on diagonal
elements. Another use of `DenseRange.equalizer` proves
`infiniteAdeleNorm_tower`.

`adeleNorm_tower` combines the infinite identity with the finite
coordinate identities by product and finite-adele extensionality. All
restrictedness obligations were already discharged by the original
norm constructions. `ideleNorm_tower` then follows by extensionality of
units, since the underlying adele of the idele norm is the adelic norm.
Finally, quotient induction chooses an actual idele representative;
`ideleClassNorm_mk` converts each class norm into the class of the
corresponding idele norm, and `ideleNorm_tower` proves the equality.

## Dependencies and scope

The implementation directly imports
`Langlands.Global.AdelicFunctoriality.IdeleClassNormLawsStatement` and
`Mathlib.RingTheory.Norm.Transitivity`. Through the statement's published
import closure, it uses the actual local determinant norms and their
continuity from `Extension` and `Norm`, the approximation lemmas from
`FiniteComparisonReduction`, the completed tensor comparison from
`CompletedTensorComparisonProof`, and the principal-adele norm and
quotient formulas from `IdeleClassNorm` and its norm-assembly dependencies.
The completed tensor comparison and determinant base change underpin the
published principal formula; they are not supplied as assumptions here.

The proof uses no global reciprocity theorem, global fundamental class,
second norm-index inequality, or global first-cohomology vanishing.
It proves the tower component only. The separately stated
`IdeleClassNormInclusionPower` and the conjunction `IdeleClassNormLaws`
are not proved by this module.

## Original sources and provenance

Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea edition
(2009), Chapter VI section 1, printed p.20 (PDF p.29), uses norm
transitivity for arbitrary finite towers in the second norm-index lemma
and its displayed index factorization. Printed pp.19–21 (PDF pp.28–30)
were read for context. The discussion applies these elementary norm laws
to the second inequality; that inequality is not an input to the present
proof. Registered source: `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata dated 23 January 2009 (PDF p.202) were read and contain
no correction to the cited passage.

J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII
section 6, Lemma 6.1, printed p.214 (PDF p.223), was also read. Its
commutative diagram and norm-after-inclusion identity occur in a
particular Galois setting. This is context for the target's source map;
it is not used to infer an arbitrary-tower theorem from a special case.
Registered source: `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
No separate errata note for either source was present in the supplied
project notes. The pinned Milne version's front matter records the
corrections incorporated through version 4.03.

The continuity and product-density route is an internal derivation by
Worker 107 from the cited published Library and Mathlib results. It is
not claimed to reproduce a proof written out in either original source.
Worker 107 is the sole author of this Lean/Markdown pair. No unpublished
peer draft was reused.
