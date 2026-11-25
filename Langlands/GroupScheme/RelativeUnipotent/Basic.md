# Relative vector-bundle additive groups and finite normal series

This module defines geometric predicates. It asserts neither existence of a
filtration nor vanishing of torsors. All schemes and group schemes are actual
objects of the Library, over an arbitrary `S : Scheme.{u}`. The definitions
impose no noetherian, connectedness, nonemptiness, or field hypothesis.

## Finite locally free modules and linear bundle data

`Langlands.GroupScheme.RelativeUnipotent.IsFiniteLocallyFree M`, for
`M : S.Modules`, requires one `SheafOfModules.LocalGeneratorsData` whose
generators are both locally free data and of finite type. The covering opens
`q.X i` cover the base; the canonical maps from free module sheaves on
`(q.generators i).I` to the restrictions of `M` are isomorphisms; and each
generator index type is finite. There is no fixed cardinality for those index
types. Thus the finite local rank can vary between components. The cover itself
can be infinite.

These are isomorphisms of sheaves of modules over the structure sheaf, so on
overlaps their transitions are linear. This uses Mathlib's actual locally free
and finite-type local-generator conditions, with both conditions on the same
data. It refines the general local-freeness convention implemented by
`SheafOfModules.IsLocallyFree` and allows more ranks than the Library's
fixed-rank predicate `Langlands.Scheme.Modules.IsLocallyFreeOfRank`.

`sectionPullback M b`, for a morphism `b : T' ⟶ T` in `Over S`, is the
canonical map from global sections of `T.hom* M` to global sections of
`T'.hom* M`. It applies the existing `Langlands.SchemeModule.pullbackSection`
along `b.left`, then the canonical `Scheme.Modules.pullbackComp` isomorphism,
then `Scheme.Modules.pullbackCongr` for `Over.w b`. These are the actual
module-pullback operations; no alternative transition maps are supplied.

`IsVectorBundleAdditive V`, for an actual `V : GroupScheme S`, requires
affineness and smoothness of its structural morphism, an actual finite locally
free module sheaf `M`, and multiplicative-group equivalences, for every test
`T : Over S`,

```text
(T ⟶ V.X) ≃* Multiplicative Γ(T.hom* M, ⊤).
```

The equivalences commute with precomposition on the left and
`sectionPullback M` on the right. `Multiplicative` only rewrites the additive
group law of module sections in the multiplicative notation for group-scheme
points. The represented group is therefore the additive bundle group of one
fixed finite locally free sheaf, with its linear structure transported through
these natural equivalences. Merely having local additive-group charts with
unrestricted group automorphisms does not satisfy this definition.

Affineness and smoothness are standard consequences of being the additive
group of a finite locally free sheaf; the predicate records them explicitly
alongside its representing data. This gives consumers direct access to these
geometric properties without requiring a new representability construction.
It does not assert that a representing group exists for every module sheaf.
No global frame, fixed finite rank, or trivialization of `M` is required.

## Finite geometric series

`HasVectorBundleSeries n H` recursively encodes a series of length `n`.
At length zero, `SubgroupFunctor.range (𝟙 H) = ⊥` says that all points of
`H` on every test scheme are the identity. By the functor of points this is
the trivial group scheme over `S`, not merely a group with trivial field-valued
points.

At length `n + 1` there are actual group schemes `K`, `V`, homomorphisms
`j : K ⟶ H` and `q : H ⟶ V`, and the following conditions:

- `j` is a closed subgroup and `K` is smooth over `S`;
- its all-test image subgroup functor is normal in `H`;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q` holds;
- `V` satisfies `IsVectorBundleAdditive`;
- `K` has a series of length `n`.

The reused quotient predicate means that the underlying scheme map of `q`
is flat, surjective and locally of finite presentation, and its actual scheme
kernel has exactly the image subgroup functor of `j` on every test. Thus it
encodes a represented fppf sheaf quotient. It does not demand surjectivity of
`H(T) → V(T)` on each original test. The closed immersion identifies `K`
with that kernel. Recursively composing the closed kernel inclusions gives a
descending series starting at `H` and ending in the trivial group; each kernel
is normal in its preceding term. No assertion of normality in the whole
initial group is needed.

`HasFiniteVectorBundleSeries H` is `∃ n, HasVectorBundleSeries n H`.
There is no torsor, cocycle, section, or cohomology condition in either series
predicate. There is no `ConnectedSpace` condition on the total space of any
term. If the initial group is affine over `S`, each subsequent kernel is affine
over `S` by its closed immersion. The quotient groups have affineness and
smoothness explicitly in their vector-bundle predicate. Zero-rank quotients
and length zero are allowed.

## Source and provenance

Brian Conrad, *Reductive group schemes* (2014), source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
PDF and printed page numbers agree.

Theorem 5.4.3, p.174, with proof pp.175–177, constructs a descending
filtration of the relative unipotent radical by smooth closed subgroups with
vector-bundle additive quotients. Lemma 5.4.4 and its proof on p.176 supply
the compatible linear structure, rather than arbitrary additive-group forms.
The notation `W(E)` there is the additive group scheme underlying a vector
bundle `E`. `IsVectorBundleAdditive` records that meaning by its natural
sections functor and explicit smoothness and affineness.

The local-generator implementation of finite local freeness and the recursive
normal-series interface are internal formulations of this geometric data.
The source supplies the stronger canonical filtration: its terms are normal
in `P`, it has commutator bounds, and it is compatible with automorphisms
and base change. Those extra conclusions are not part of this module.
Corollary 5.4.8, p.179, uses precisely the vector-bundle filtration to reduce
torsor vanishing over an affine base to affine vanishing for vector bundles.
The corresponding existence and vanishing propositions belong to separate
statement modules.
