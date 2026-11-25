# Topology of Renard's chamber in the actual split-component space

This module states the topological meaning of the nonstrict chamber already defined
in [RenardLeviCones](RenardLeviCones.md). It introduces no second chamber or torus
space. The declaration is a proposition definition; its proof is not given here.
The theorem `Langlands.BruhatTits.Cartan.RenardLeviCones.leviChamberTopology` in
`RenardLeviChamberTopologyProof` proves it.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, source id `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:

- V.3.14–V.3.15, printed p.113 / PDF p.119, defines `Δ(P)` by restriction to the
  split component. V.3.15 gives the strict and nonstrict chambers and obtains their
  versions in `𝔞_M` by exchanging roots and coroots.
- V.3.16, printed p.114 / PDF p.120, explains the open face, its closure and the
  central-direction decomposition on the dual side.
- V.3.21, printed p.116 / PDF p.122, uses the chamber and its closure to define
  `M^{++}` and `M^+` through the valuation `H_M`.

The source's bar notation in V.3.15 is expressed here by actual topological
closure on `𝔞_M`. Nonemptiness, openness and closedness are the elementary real
linear algebra assertions underlying this interpretation. They are included as
explicit conclusions, rather than assumed. This is a derived clarification of
these passages, not a new claim about the group topology.

## Declaration and hypotheses

`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviChamberTopologyStatement.{u}`
quantifies over:

- a field `k`, an actual connected reductive group scheme `G`, a commutative group
  scheme `T` and a maximal split torus inclusion `i : T.toGrp ⟶ G`;
- a generic cocharacter `ν`, which selects the positive roots, and a subset `J`
  of the simple relative roots;
- a closed representative `j : L ⟶ G` of the actual standard Levi
  `standardLevi i ν J`;
- an actual split component `a : A.toGrp ⟶ L` and a morphism `f : A ⟶ T` with
  `CommGroupScheme.groupHom f ≫ i = a ≫ j`.

These geometric hypotheses distinguish the assertion from a false closure claim
for arbitrary morphisms and arbitrary restricted functionals. For example,
restriction along an arbitrary morphism could send a selected root to zero,
making its strict inequality impossible.

The topology on `V A = ℝ ⊗[ℤ] cocharacterLattice A` is fixed locally to
`moduleTopology ℝ (V A)`, the canonical real vector-space topology. No topology
on `k` or its rational points enters this statement. The field is arbitrary:
this real linear algebra consequence extends the source's local-field setting
without a splitting or characteristic restriction on `G`. All group schemes
are in the field's universe `u`; no additional representation space is involved.

## Conclusions

For these data, with the specified topology, the statement is the conjunction:

1. `chamber i ν J f` is nonempty;
2. that chamber is open in the whole space `V A`;
3. `closedChamber i ν J f` is closed in that space;
4. `closure (chamber i ν J f) = closedChamber i ν J f`.

The two sets are exactly the existing predicates `pair A β x > 0` and
`pair A β x ≥ 0` for all `β ∈ restrictedSimpleRoots i ν J f`. There is no
nonemptiness, linear independence or closure equality premise. The empty-root
case is included: both inequality sets are then the whole space, including when
`V A` has dimension zero. Central directions are retained; no assertion of
pointedness is made.

## Remaining proof and relation to existing work

[ParabolicChamberStatements](../../Representation/LanglandsClassification/ParabolicChamberStatements.md)
states the ambient coroot-face topology on `Vstar T` and split-component
comparison assertions. The present proposition concerns the published root
inequalities on the actual `V A` used by `RenardLeviCones`. Neither that ambient
closure assertion nor the norm/valuation comparisons in `RenardLeviCones` alone
is this statement.

A proof must establish a positive chamber point from the actual Levi and
split-component data. After that, continuity of the finitely many linear
functionals gives openness and closedness, and perturbing a nonstrict point by
a positive multiple of the chamber point gives the closure inclusion. This is a
proof plan only; no theorem implementing it is included here. The proposition
does not settle the separate source issue with (V.3.21.1), the lattice partition,
or any remaining split-component realization assertion.
