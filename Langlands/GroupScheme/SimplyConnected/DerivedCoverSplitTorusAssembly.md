# Assembling maximal split tori through a simply connected derived cover

Author: Worker 1470.

This internal support module bundles three published propositions and proves
that, together, they imply
`SimplyConnectedDerivedCoverSplitTorusStatement`. It also proves the
composition and scalar-extension lemmas used in that implication. All
declarations have arbitrary universe `u`; their fields are arbitrary, including
imperfect fields and positive characteristic.

## Bundled premises and scope

`SimplyConnectedDerivedCoverSplitTorusPremises.{u}` is the conjunction of:

1. `DerivedMaximalSplitTorusStatement.{u}`, imported from
   [`Derived.MaximalSplitTorusStatement`](../Derived/MaximalSplitTorusStatement.md).
   This supplies a maximal split torus `j : S_D.toGrp ⟶ D`, a closed
   homomorphism `e : S_D ⟶ S`, and the equality
   `j ≫ d = CommGroupScheme.groupHom e ≫ i`.
2. `SimplyConnectedCoverSplitTorusStatement.{u}`, imported from
   [`SimplyConnected.SplitTorusStatement`](SplitTorusStatement.md).
   Applied to the supplied cover of `D` and to `j`, this supplies a maximal
   split torus `i_C : S_C.toGrp ⟶ C` and `f : S_C ⟶ S_D`, with
   `i_C ≫ π = CommGroupScheme.groupHom f ≫ j` and
   `IsCentralIsogeny (CommGroupScheme.groupHom f)`.
3. `SplitTorusIsogenyCocharacterStatement.{u}`, imported from
   [`Rational.SplitTorusIsogenyCocharacter`](../Rational/SplitTorusIsogenyCocharacter.md).
   For the isogeny `f` between these split tori, it supplies integral
   injectivity and a finite integral cokernel, together with rational and real
   bijectivity. The assembly uses only the latter two conclusions.

`simplyConnectedDerivedCoverSplitTorusStatement_of_inputs` assumes these three
propositions separately and concludes the published
`SimplyConnectedDerivedCoverSplitTorusStatement.{u}`.
`SimplyConnectedDerivedCoverSplitTorusPremises.statement` gives the same
implication from the bundled premise.

The module proves none of the three input propositions. It therefore does not
give an unconditional proof of the derived-cover statement. In particular, it
does not construct the derived torus or the covering torus without those
premises.

## Actual cocharacter maps

The helper lemmas are in `Langlands.GroupScheme.RealTorusSpace`. For a field
`k : Type u`, let `A`, `B` and `T` be arbitrary commutative group schemes over
`Spec k`, and let `f : A ⟶ B` and `e : B ⟶ T`. These lemmas do not require
the group schemes to be split tori.

`cocharacterMapInt_comp` identifies postcomposition by `f ≫ e` with the
composition of `cocharacterMapInt f` and `cocharacterMapInt e`. Its proof is
extensionality on actual cocharacters and associativity of group-scheme
homomorphisms. `cocharacterMapReal_comp` proves the corresponding real
identity using `LinearMap.baseChange_comp`.

`cocharacterMapInt_baseChange_rat_injective` assumes that the underlying
scheme morphism of `e` is a monomorphism and proves injectivity of
`(cocharacterMapInt e).baseChange ℚ`. It reuses
`cocharacterMapInt_injective` from
[`Rational.SplitCentralEmbedding`](../Rational/SplitCentralEmbedding.md)
and applies `Module.Flat.lTensor_preserves_injective_linearMap` to the flat
`ℤ`-module `ℚ`.

`cocharacterMap_comp_injective_range` assumes that `groupHom e` is a closed
immersion, that `(cocharacterMapInt f).baseChange ℚ` is bijective, and that
`cocharacterMapReal f` is bijective. It proves rational and real injectivity
of the maps of `f ≫ e`, with their ranges equal to those of `e`.
Closed immersion supplies the monomorphism needed for rational injectivity;
real injectivity of `e` is the published `cocharacterMapReal_injective`.
Composition preserves injectivity. Bijectivity of the maps of `f` gives full
range, so `LinearMap.range_comp_of_range_eq_top` gives both range equalities.

All maps are the published postcomposition map on `cocharacterLattice` and
its scalar extensions from
[`Rational.RelativeCentralDirections`](../Rational/RelativeCentralDirections.md).
The proof introduces no coordinates.

## Conditional assembly

Given `IsSimplyConnectedDerivedCover d π` and `IsMaximalSplitTorus i`, the
proof applies the derived-torus premise using the connected reductivity of
`G` and `IsDerivedSubgroup d`. It then applies the covering-torus premise
using `IsSimplyConnectedCover π`. The maximal split-torus predicates of
`S_C` and `S_D` supply their splitness, and the central isogeny of `f`
supplies its isogeny predicate. The third premise now gives the two
bijectivity hypotheses of `cocharacterMap_comp_injective_range`.

The witnesses from these premises are retained as the witnesses of the target.
Associativity and the two commuting squares prove
`i_C ≫ π ≫ d = CommGroupScheme.groupHom (f ≫ e) ≫ i`. The range lemma gives
the remaining rational and real conclusions. There is no claim of
surjectivity onto `S`, no assertion about `k`-points, and no integral
conclusion for `f ≫ e`.

## Internal provenance

This is a formal combination of the three named Library propositions,
the published injectivity lemmas, and Mathlib's scalar-extension and
linear-map range lemmas. The paired documents linked above describe the
geometric statements and their source provenance. This module introduces no
additional geometric assertion or external mathematical premise; its
conditional nature is explicit in both its Lean types and this description.
