# Rational-point decompositions for compatible represented parabolics

Authors: Worker 1754 and Worker 1291. Worker 1754 authored the original
draft; Worker 1291 checked the source and published interfaces and clarified
the documentation. Module
`Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionStatement`,
namespace `Langlands.GroupScheme`. The declaration
`NestedParabolicPointDecompositionStatement.{u} : Prop` is a statement; no
decomposition is proved in this file.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.1.4, the paragraph immediately preceding
the Lemma, printed p.136 / PDF p.142. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Lemma and proof continue on printed p.137 / PDF p.143.

This is a derived formulation of the structural equalities used there, for
the same represented triples and rational-point compatibility as the published
`Langlands.Aubert.General.RepresentedParabolic.LeviParabolicTransitivityStatement`.
It isolates a prerequisite for that functor theorem. The rational-point
hypotheses and the exact supplied inner radical are part of the formulation;
the source does not state this precise quantifier structure.

## Inputs

The field `k : Type u` has `[Field k] [ValuativeRel k] [TopologicalSpace k]`
`[IsNonarchimedeanLocalField k] [T2Space k]`. Thus the statement includes
nonarchimedean local fields of either characteristic and arbitrary field
universe. `G` is a connected reductive group scheme over `Spec k`.
No topology, local compactness or nonarchimedean-group assumption on `G(k)`
is needed to state these algebraic identities.

There are three supplied actual parabolic triples:

- `p : P ⟶ G`, with Levi `m : M ⟶ P`, geometric unipotent radical
  `n : N ⟶ P`, and an isomorphism of the actual multiplication morphism
  `subgroupMultiplication m n`;
- `q : Q ⟶ G`, with Levi `l : L ⟶ Q`, geometric unipotent radical
  `uQ : U ⟶ Q`, and the corresponding multiplication isomorphism;
- `pL : PL ⟶ L`, with Levi `mL : M ⟶ PL`, geometric unipotent radical
  `nL : NL ⟶ PL`, and the corresponding multiplication isomorphism.

The eight auxiliary group schemes, in addition to `G`, and all nine
subgroup morphisms are quantified explicitly. In particular the inner Levi
is the very same group scheme `M`,
not an unspecified isomorphic replacement. The predicates are the published
`IsParabolicSubgroup`, `IsRationalLeviSubgroup` and
`LeviSubgroup.IsGeometricUnipotentRadical`. The last requires the radical
property both over `k` and over its algebraic closure. The multiplication
is a morphism of schemes over `k`; it is not claimed to be a homomorphism
from the direct product group scheme.

The local names are subgroups of `rationalPoints G`. Each is the range
`(rationalPoints.map f).range` for the following actual map `f` into `G`:

| Subgroup | Map `f` |
| --- | --- |
| `P₀` | `p` |
| `Q₀` | `q` |
| `L₀` | `l ≫ q` |
| `N₀` | `n ≫ p` |
| `U₀` | `uQ ≫ q` |
| `PL₀` | `pL ≫ l ≫ q` |
| `NL₀` | `nL ≫ pL ≫ l ≫ q` |

These ranges are definitionally the `pointImage` subgroups used by the represented
parabolic functors. The present file uses `rationalPoints.map` directly so
that the geometric statement need not import those representation functors.

The compatibility hypotheses are exactly:

1. `P₀ ≤ Q₀`;
2. `mL ≫ pL ≫ l ≫ q = m ≫ p`, as group-scheme morphisms from the
   original `M` to `G`;
3. `PL₀ = L₀ ⊓ P₀`.

The statement adds no supplied standardness, maximal torus, cocharacter
presentation, all-test containment, radical inclusion or product
decomposition. No parabolic is required to be proper.

## Conclusions

The conjunction consists of three identities in the ambient group `G(k)`:

1. `NL₀ = L₀ ⊓ N₀`. Thus the particular supplied inner radical is
   identified with the intersection of the outer Levi and the fine radical.
2. `N₀ = (L₀ ⊓ N₀) U₀`.
3. `P₀ = PL₀ U₀`.

The last two equalities are equalities of sets, with pointwise group
multiplication and factors in the displayed order: `A * B` is the set of
all `a * b` with `a ∈ A` and `b ∈ B`. The radical of `Q` is the right
factor in both products. Together with the first
they also give `N₀ = NL₀ U₀` and `P₀ = (L₀ ⊓ P₀) U₀`.
They assert existence of factorizations. The statement does not separately
assert a scheme-level product isomorphism or a choice of factors.

## Relation to the source and the functor theorem

The paragraph before Renard's VI.1.4 Lemma starts with semistandard
parabolics `P = MN ⊂ Q = LU` and states that `L ∩ P = M(L ∩ N)` is a
parabolic of `L`, that `N = (N ∩ L)U`, and that `(L ∩ P)U = P`.
Here `PL = M NL` is already given as an actual parabolic triple, and its
rational image is required to be `L₀ ∩ P₀`. The first conclusion records
the radical identification needed to use that given triple.

The Markdown for `LeviParabolicTransitivityStatement` motivates the
comparison with the source's semistandard framework using the common Levi
embedding and maximal split tori. Applying that framework here requires
proof: one must justify passing from the supplied rational-point
containment to algebraic containment, for example through an appropriate
rational-point density theorem, and then identify the supplied inner
radical with the intersection. None of these comparisons is proved here or
added as a hypothesis.

The source's Jacquet proof uses these decompositions and the modulus
identity. The present statement contains no functors or modulus characters
and establishes none of their properties. Conversely the published
dynamic nested-parabolic theorem requires supplied dynamic presentations
and compatibility; importing that theorem alone does not prove this
statement for the arbitrary represented triples here.

## Remaining proof obligations

A proof must derive these identities from precisely the supplied triples
and the three compatibility hypotheses. In particular it must justify
every density or descent passage it uses, identify the radical of the
given `PL`, and prove that the coarse radical lies in the fine radical and
that the ordered products exhaust the displayed groups. The statement
does not construct an inner parabolic or an ambient extension from two
triples. Those are separate structural existence questions.

After this proposition is independently accepted and published, its exact
proof is a separate prerequisite. Only a proof of that proposition can
supply the structural equalities for an unconditional proof of the full
represented VI.1.4 functor theorem.
