# Reflection of connected reductivity and semisimplicity along algebraic extensions

Author: Worker 1408.

This module defines three propositions and proves none of them:

- `Langlands.GroupScheme.ConnectedReductiveAlgebraicExtensionReflectionStatement.{u}`;
- `Langlands.GroupScheme.SemisimpleAlgebraicExtensionReflectionStatement.{u}`;
- `Langlands.GroupScheme.AlgebraicExtensionReflectionStatement.{u}`, the
  conjunction of the first two.

The package is the proof target. Its two components are named so that a
consumer can use either implication separately. The only import is the
unchanged module `Langlands.GroupScheme.Reductive.Semisimple`, which in turn
imports `Langlands.GroupScheme.Reductive.Basic`. No predicate, base-change
functor or cover-existence interface is changed. The interface was specified
by task `43a6466f-3523-445c-bfac-3ef6a3f965b8`, which Worker 1347 published as
a prerequisite of the arbitrary-field cover-existence task
`a41119fb-a633-4b81-a979-4b08e9ddbb15`.

## Quantifiers and actual base change

The universe `u` is arbitrary. Each component quantifies, separately, over
every pair `k K : Type u`, every field structure on each, every
`Algebra k K`, every proof of `Algebra.IsAlgebraic k K`, and every actual
`G : GroupScheme (Spec (CommRingCat.of k))`. A group scheme is the Library's
group object in the category of schemes over the indicated base.

`Algebra.IsAlgebraic k K` is Mathlib's class asserting that every `x : K` is
algebraic over `k`: some nonzero polynomial `p : k[X]` has `aeval x p = 0`.
This is the only condition on the extension. It may be infinite, inseparable
or purely inseparable, and it may be non-normal. There is no perfectness or
characteristic restriction, so infinite and inseparable algebraic extensions
of imperfect fields of positive characteristic are included. The extension
`K` need not be algebraically closed and need not embed in any chosen closure
in a specified way. Transcendental extensions are excluded; this module makes
no claim about them.

Write

```text
b   = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k,
G_K = (GroupScheme.baseChange b).obj G.
```

These expressions abbreviate the actual terms written inline in Lean. The
unchanged functor `GroupScheme.baseChange b` is `(Over.pullback b).mapGrp`:
its object is the scheme pullback of `G` along `b`, with the induced group
law. The components are exactly

1. `IsConnectedReductive G_K → IsConnectedReductive G`;
2. `IsSemisimple G_K → IsSemisimple G`.

In each implication the sole premise on `G` is the corresponding property of
`G_K`. Smoothness, affineness, connectedness, finite type, reductivity,
existence or finiteness of a centre, and effective descent of `G` are not
inputs; a proof must derive whatever it needs.

## The connected-reductive predicate

Both sides of the first component, and the first field of each side of the
second, use the unchanged structure `IsConnectedReductive` from
`Reductive.Basic`. For a group scheme `H` over a field `F` it has four fields:

- `smooth : Smooth H.X.hom` and `isAffineHom : IsAffineHom H.X.hom` for the
  structural morphism to `Spec F`;
- `connectedSpace : ConnectedSpace H.X.left` for the underlying topological
  space;
- `hasTrivialGeometricUnipotentRadical`, which is
  `HasTrivialUnipotentRadical` of the base change of `H` along
  `toAlgebraicClosure F = Spec.map (CommRingCat.ofHom (algebraMap F
  (AlgebraicClosure F)))`.

Here `AlgebraicClosure F` is Mathlib's specific algebraic closure.
`HasTrivialUnipotentRadical` over a field `L` says: for every actual group
scheme `U` over `L` and homomorphism `i : U ⟶ H_L` whose underlying morphism is
a closed immersion, if `U` is smooth, has connected underlying space and is
unipotent, and `SubgroupFunctor.range i` is normal, then that range is the
trivial subgroup functor. Unipotence means that every nonzero
finite-dimensional matrix representation has a nonzero fixed vector.

Thus the premise of the first component concerns `AlgebraicClosure K` and
base change of `G_K`, whereas the conclusion concerns `AlgebraicClosure k`
and base change of `G`. These are different fields and different iterated
pullbacks; their comparison is a proof obligation, not part of the statement.

## The semisimplicity predicate and the full centre

Both sides of the second component use the unchanged structure
`IsSemisimple` from `Reductive.Semisimple`. Its fields are
`isConnectedReductive`, as above, and `hasFiniteCenter : HasFiniteCenter H`.
The latter asserts that there exist an actual group scheme `Z` over the same
field and an actual homomorphism `z : Z ⟶ H` such that
`IsSchemeTheoreticCenter z` and `IsFinite Z.X.hom`.

`IsSchemeTheoreticCenter z` means that the underlying scheme morphism of `z`
is a closed immersion and `SubgroupFunctor.range z = center H`. The range on a
test scheme `T` consists of the `T`-points of `H` that factor through `z`. A
`T`-point `x` lies in the centre when, for every morphism `T' ⟶ T` of test
schemes, the restriction of `x` to `T'` commutes with every `T'`-point of `H`.
The equality is equality of subgroup functors on all test schemes over the
field, including nonreduced ones. The representative need not be smooth,
reduced or connected, so its nilpotents are retained. Finiteness is
finiteness of the structural morphism of this actual representative; it is
not finiteness of rational points or of a reduced centre.

Consequently the conclusion of the second component requires the existence,
over `k`, of an actual finite representative of the full centre of `G`. The
first component is not a premise of the second; the package simply records
both.

## Sources and derived provenance

The original source is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Printed
page `p` is PDF page `p + 16`. The following were read in full:

- 6.44 and 6.46, printed p.135 (PDF p.151), in a section whose algebraic
  groups are all affine: a connected group variety over `k` is semisimple,
  respectively reductive, when the radical, respectively unipotent radical,
  of its base change to an algebraic closure `k^a` is trivial.
- Proposition 19.5, printed pp.398–399 (PDF pp.414–415): for an algebraic
  group `G` over `k` and every field `k'` containing `k`, `G` is semisimple
  if and only if `G_{k'}` is.
- Proposition 19.10, printed p.400 (PDF p.416): a reductive group is
  semisimple if and only if its centre is finite; the preceding paragraph
  notes that the centre need be neither smooth nor connected.
- Proposition 19.13, printed p.400 (PDF p.416): for an algebraic group
  variety `G` over `k` and every field `k'` containing `k`, `G` is reductive
  if and only if `G_{k'}` is.

The two components select the reflection directions of Propositions 19.13 and
19.5 and restrict them to algebraic extensions. The Library's semisimplicity
predicate is the finite-centre characterization of Proposition 19.10 applied
to its connected-reductive predicate. The complete retained author errata,
source `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, was read.
Its Chapter 6 entries concern 6.19 and Example 6.48, and its Chapter 19 entry
concerns Definitions 19.7 and 19.8; none corrects the items cited here.

This is a derived formulation on the Library's actual group schemes. Milne
does not write these Lean interfaces, the specific closure
`AlgebraicClosure`, or the existential full-centre representative. His
algebraic groups are of finite type by convention, and his reductive and
semisimple groups are affine, smooth and connected by definition. The Lean
proposition quantifies over every actual `G` and assumes only the predicate
after algebraic scalar extension.

The restriction to algebraic extensions is internal. It is the case needed by
the cover-existence task, where a source constructed by finite Galois descent
must be shown semisimple, and it admits a route through existing Library
interfaces. That route is recorded here only as provenance; this module proves
nothing:

- For algebraic `K/k`, `AlgebraicClosure K` is an algebraic closure of `k`,
  and Mathlib supplies the `k`-algebra isomorphism
  `IsAlgClosure.equiv k (AlgebraicClosure K) (AlgebraicClosure k)`.
- `HasTrivialUnipotentRadical.baseChange_of_bijective` in
  `Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange` transports
  radical triviality along this isomorphism. `Descent.pullbackComparison` in
  `Langlands.GroupScheme.Descent.Data` identifies the iterated pullbacks, the
  composite base maps agreeing by the scalar tower and the isomorphism's
  `commutes` law.
- Smoothness reflects by fpqc descent along `b` (`fieldExtension_fpqc` in
  `Langlands.GroupScheme.BaseChangeReflection`), affineness by
  `Langlands.AlgebraicGeometry.fieldExtensionAffineDescent`, and
  connectedness through the surjective pullback projection to `G`.
- The finite full-centre field is supplied by
  `IsSemisimple.hasFiniteCenter_of_fieldExtension` in
  `Langlands.GroupScheme.Reductive.FiniteCenterReflection`.

The centre step holds for every field extension; algebraicity is used only to
identify the two algebraic closures.

## Relation to other propositions

`Langlands.GroupScheme.SemisimpleFieldReflectionStatement` in
`Reductive.SemisimpleFieldReflectionStatement` states semisimplicity
reflection along every field extension, including transcendental ones. It
implies the second component here, but nothing here implies it; its broader
scope is unchanged. The ascent directions are the separate propositions
`ConnectedReductiveFieldExtensionStatement` in
`Reductive.FieldExtensionStatement` and `IsSemisimpleFieldExtensionStatement`
in `SimplyConnected.FieldExtensionStatement`.

This module does not assert reflection along transcendental extensions,
descent of simple connectedness, existence of a covering cocycle or
completion of `SimplyConnected.CoverExistenceStatement`, which it leaves
unchanged.
