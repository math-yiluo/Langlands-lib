# Geometric compatible refinements and minimal-parabolic split components

Author: Worker 1445. This internal derived development combines the published
compatible-cocharacter construction and minimality bridge with the proved
dynamic-to-geometric parabolic recognition theorem. Its original-Levi corollary
reuses Worker 1264's supplied-presentation construction. It asserts no additional
literature theorem.

All fields have the arbitrary universe `u`. Groups, morphisms, cocharacters and
split tori are defined over the original field, including imperfect fields and
arbitrary characteristic. Every subgroup-functor equality and inclusion is on
every test scheme.

## Certified geometric refinement

`isParabolicFunctor_dynamic hG χ` proves geometric parabolicity of
`Dynamic.parabolic χ` for a connected reductive group `G`.
The actual affine dynamic representative is closed and represents this functor.
The published `isParabolicSubgroup_of_range_eq_dynamicParabolic` proves that
representative geometrically parabolic. Its group, inclusion and range equality
therefore witness the published `IsParabolicFunctor` predicate. No
`ParabolicDynamicStatement` premise is used.

The selected definition `IsSplitTorus.parabolicCompatibleCocharacter hB hG b ν`
returns a cocharacter `ζ` of the supplied split torus `B` and certificates that

```text
Z_G(ζ) = torusCentralizer b,
P_G(ζ) is geometrically parabolic,
P_G(ζ) ≤ P_G(ν),
U_G(ν) ≤ U_G(ζ).
```

Here each ambient cocharacter is `CommGroupScheme.groupHom` of the indicated
lattice element followed by the given actual homomorphism `b : B.toGrp → G`.
The map `b` need not be injective or closed, and `ν` may be zero.
The definition uses `compatibleCentralizingCocharacter` and its three published
certificates, then adds the preceding geometric-parabolicity certificate.
Affineness and local finite type required by that construction follow from
connected reductivity and smoothness. The result retains both original dynamic
inclusions.

## Ambient maximality from a presenting cocharacter

`IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_presentingCocharacter`
assumes an actual minimal parabolic `p : P → G`, a connected reductive closed
subgroup `i : L → G` with range contained in `p`, a split component
`a : A.toGrp → L`, and that `i` represents the whole-torus centralizer of
`a ≫ i`. It also assumes a cocharacter `ν` of `A` for which
`P_G(groupHom ν ≫ a ≫ i) = range p`. It proves that `a ≫ i` is a maximal
split torus in the ambient group `G`.

The proof applies the published
`IsSplitComponent.isMaximalSplitTorus_of_minimalParabolic_compatible_extensions`.
For any ambient maximal split extension `b : B.toGrp → G` with actual
factorization `f ≫ b = a ≫ i`, compose `ν` with `f` to obtain a cocharacter
`μ` of `B`. Its ambient dynamic parabolic is exactly `range p`.
The certified geometric refinement above supplies a cocharacter `ζ` of `B`
with the whole-`B` centralizer, genuinely parabolic dynamic functor and
parabolic contained in `range p`. These discharge every compatible-extension
input of that published maximality theorem.

That theorem uses minimality to identify the refined parabolic with `range p`.
The given subgroup `L` then has full dynamic parabolic for the induced
cocharacter. Its reductivity forces full centralizer. Thus the extension torus
is central in this original `L`; maximality among its central split tori makes
the extension map an isomorphism, proving ambient maximality. The present
module supplies the geometric compatible refinement that this earlier theorem
left as an explicit input.

## The specified original Levi

`IsRationalLeviSubgroup.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic`
assumes the actual rational Levi `l : L → P`, connected reductivity of `G`,
minimality of `p : P → G`, a supplied dynamic presentation
`(Dynamic.parabolic χ).IsRepresentedBy p`, and any specified split component
`a : A.toGrp → L`. It proves `IsMaximalSplitTorus (a ≫ l ≫ p)`.

The published
`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
constructs `ν` in this original split component, presents the original
parabolic and identifies the whole-component centralizer with `range (l ≫ p)`.
The given Levi and parabolic are closed, so their composite is closed and
monic. Its range lies in `range p`. These data discharge the preceding
ambient-maximality theorem.

The initial dynamic presentation remains a hypothesis of this corollary.
Constructing it for an arbitrary geometric minimal parabolic, assembling the
specified solvable-radical factor, and proving the exact unconditional
`MinimalParabolicLeviCentralizerStatement` remain obligations of the host task.
