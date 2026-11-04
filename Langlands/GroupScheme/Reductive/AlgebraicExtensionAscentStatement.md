# Ascent of connected reductivity and semisimplicity along algebraic field extensions

This module defines three propositions and proves none of them.

- `Langlands.GroupScheme.ConnectedReductiveAlgebraicExtensionAscentStatement`
- `Langlands.GroupScheme.SemisimpleAlgebraicExtensionAscentStatement`
- `Langlands.GroupScheme.AlgebraicExtensionAscentStatement`, the conjunction
  of the first two at the same universe `u`.

## Quantifiers

Each component quantifies over a universe `u`, fields `k K : Type u`, an
instance `Algebra k K` and an instance `Algebra.IsAlgebraic k K`, and an
actual group scheme `G : GroupScheme (Spec (CommRingCat.of k))`.

Algebraicity of `K` over `k` is the only hypothesis on the fields. The
extension may be infinite, inseparable or purely inseparable. The field `k`
may be imperfect of positive characteristic. `K` need not be algebraically
closed, normal or separably closed. The trivial extension `K = k` and the
algebraic closure of `k` are both included. No hypothesis is placed on `G`
beyond the hypothesis of each implication, and no root datum, torus, pinning,
cover or ascent theorem appears as data or as an assumption.

## The actual base change

The base map is the actual scheme morphism

`b = Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k`,

written inline in both components. The functor is the published
`GroupScheme.baseChange b` from `Langlands.AbelianScheme.GroupScheme`, which
is `(Over.pullback b).mapGrp`. In this documentation,

`G_K = (GroupScheme.baseChange b).obj G`

denotes the fibre product `G ×_{Spec k} Spec K` over `Spec K` with the
pulled-back group law. No other model of the base change is used.

## The components

- `ConnectedReductiveAlgebraicExtensionAscentStatement` asserts
  `IsConnectedReductive G → IsConnectedReductive G_K`.
- `SemisimpleAlgebraicExtensionAscentStatement` asserts
  `IsSemisimple G → IsSemisimple G_K`.

Each component states only the direction from `k` to `K`. Neither asserts
that a property of `G_K` descends to `G`. Reflection along algebraic
extensions is the subject of a separate statement task.

## Meaning of the predicates

The module imports `Langlands.GroupScheme.Reductive.Basic` and
`Langlands.GroupScheme.Reductive.Semisimple` and uses their predicates
unchanged.

`IsConnectedReductive H`, for a group scheme `H` over `Spec` of a field `F`,
has four fields: `H` is smooth over `Spec F`, its structure morphism is
affine, its underlying scheme is connected, and
`HasTrivialUnipotentRadical` holds for the base change of `H` along
`toAlgebraicClosure F`, the map `Spec (AlgebraicClosure F) ⟶ Spec F`.

`HasTrivialUnipotentRadical` tests every smooth connected unipotent closed
subgroup `i : H' ⟶ H_{F^alg}` whose range is normal. Its conclusion is that
the range subgroup functor of `i` equals the bottom subgroup functor on every
test scheme. This expresses triviality of the geometric unipotent radical,
the unipotent radical over an algebraic closure. The condition is not
replaced by the `F`-unipotent radical, which would give the different
pseudo-reductive condition over imperfect fields. `IsUnipotent` asks for
nonzero fixed vectors in finite-dimensional matrix representations,
following Milne 6.45.

In the hypothesis the radical is tested over `AlgebraicClosure k`. In the
conclusion it is tested over `AlgebraicClosure K`. These are different types,
and the statement does not identify them.

`IsSemisimple H` has two fields: `IsConnectedReductive H` and
`HasFiniteCenter H`. The latter asks for an actual group scheme `Z` over
`Spec F` and a morphism `z : Z ⟶ H` with `IsSchemeTheoreticCenter z` and
`Z` finite over `Spec F`. `IsSchemeTheoreticCenter z` means that `z` is a
closed subgroup and that its range subgroup functor equals the full
`center H`. The centre is tested on all schemes over `Spec F`, including
nonreduced ones. Nonreduced centres, such as `μ_p` in `SL_p` in
characteristic `p`, are therefore kept with their nilpotents. Milne
Proposition 19.10 identifies finite centre with semisimplicity for reductive
groups; the Library takes finite centre as its definition.

## Relation to other statements

The published `ConnectedReductiveFieldExtensionStatement`, in
`Langlands.GroupScheme.Reductive.FieldExtensionStatement`, and
`IsSemisimpleFieldExtensionStatement`, in
`Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`, quantify
over arbitrary field extensions, with no algebraicity instance. The two components here are their
specializations to algebraic extensions: a proof of either unrestricted
statement gives a proof of the corresponding component by ignoring the
`Algebra.IsAlgebraic` instance. This module does not import those statements,
and it does not replace them. It asserts nothing about transcendental
extensions.

This module does not state ascent of simple connectedness or of simply
connected covers, and it proves no cover-existence theorem.

## Sources and provenance

Both components are derived. Each restricts a source result to algebraic
extensions and to the Library's exact predicates.

- J. S. Milne, *Algebraic Groups* (2017), source
  `milne-2017-algebraic-groups`.
  - 6.44–6.46, printed p.135 (one-based PDF p.151), define unipotence by
    fixed vectors (6.45) and define a connected group variety over `k` to be
    reductive when its geometric unipotent radical `R_u(G_{k^a})` is trivial
    (6.46).
  - Proposition 19.13, printed p.400 (PDF p.416), states that `G` is
    reductive if and only if `G_{k'}` is reductive for any field `k'`
    containing `k`. Its proof refers to that of Proposition 19.5, printed
    pp.398–399 (PDF pp.414–415). The first component is the forward
    implication of 19.13 for algebraic `k'`.
  - Proposition 19.10, printed p.400 (PDF p.416), states that a reductive
    group is semisimple if and only if its centre `Z(G)` is finite. With
    Proposition 19.5 (semisimplicity is invariant under any field extension)
    it gives the second component under the Library's finite-centre
    convention.
- Milne's official errata, source
  `milne-2017-algebraic-groups-errata-2026-11-02`, retained snapshot dated
  2026-11-02, read in full. It corrects nothing in 6.44–6.46 or in
  Propositions 19.5, 19.10 and 19.13.

For algebraic extensions the argument is simpler than Milne's, which reduces
to an extension of algebraically closed fields and uses a spreading argument.
An algebraic closure of `K` is also an algebraic closure of `k`, so no
extension of algebraically closed fields is needed. The expected proof route
below uses only public Library and Mathlib interfaces. All its steps are
proof obligations of a successor. None of them is a hypothesis of these
propositions or a result proved in this module.

1. Algebraicity of `K` over `k` gives `IsAlgClosure k (AlgebraicClosure K)`.
   Mathlib's `IsAlgClosure.equiv` then gives a `k`-algebra isomorphism
   `AlgebraicClosure K ≃ AlgebraicClosure k`.
2. `HasTrivialUnipotentRadical.baseChange_of_bijective`, in
   `Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange`, transports
   the geometric hypothesis along the inverse isomorphism. This is a
   bijective ring map, so no ascent of unipotent radicals along a
   nonbijective map is used.
3. Two applications of `Descent.pullbackComparison`, in
   `Langlands.GroupScheme.Descent.Data`, identify the result with the base
   change of `G_K` along `toAlgebraicClosure K`. The needed equalities of
   base maps follow from `IsScalarTower.algebraMap_eq` and the `commutes`
   law of the isomorphism.
4. Smoothness and affineness are preserved by base change. Connectedness of
   `G_K` follows from `connectedSpace_baseChange_of_smooth_affine` in
   `Langlands.GroupScheme.GeometricConnectedness`.
5. For the semisimple component, `HasFiniteCenter.baseChange` in
   `Langlands.GroupScheme.Reductive.FiniteCenterBaseChange` preserves the
   full finite centre under arbitrary base change.
