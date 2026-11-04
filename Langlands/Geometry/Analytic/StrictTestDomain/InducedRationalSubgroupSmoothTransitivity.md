# Original rational subgroup smooth transitivity

This module constructs the actual lax smooth direct-image comparison for
successive original subgroup restrictions of a fixed rational domain. It
proves full smooth coefficient pullback and finite trace transitivity,
including both natural-transformation laws on the entire original smooth
coefficient category.

The namespace is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.

## Original objects, coefficients and stability

Let `K : Type u` be a complete ultrametric normed field, let `P` be a presented
strict affinoid `K`-algebra, let `G : Type u` be a topological group, and let
`ρ : RationalSpectralAction G P`. Fix open subgroups `W ≤ V ≤ U`, proofs
`k : W ≤ V`, `h : V ≤ U`, and an originally `U`-invariant rational domain
`d`. The rational presentation, local Banach spectrum, topology and restricted
actions are the original ones. All carriers share arbitrary universe `u`,
as required by the existing smooth direct-image interface.

Write

```text
X = (inclusion W).obj ((ρ.invariantRestrictionFunctor (k.trans h)).obj d),
Y = (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d),
Z = (inclusion U).obj d,

f = subgroupRestriction k ((ρ.invariantRestrictionFunctor h).obj d) : X ⟶ Y,
g = subgroupRestriction h d                                       : Y ⟶ Z,
q = subgroupRestriction (k.trans h) d                             : X ⟶ Z.
```

The direct and successive objects at level `W` are definitionally equal.
The imported `subgroupRestriction_comp` proves `f ≫ g = q` on the original
rational arrows. No equality of their maps is supplied as an assumption.

The only local geometric stability premise is

```text
HasStableNeighbourhoods Z.subgroup.toSubgroup Z.LocalSpectrum.
```

The local instances `middleStable` and `innerStable` derive the corresponding
properties of `Y` and `X` by applying the existing
`subgroupRestriction_hasStableNeighbourhoods` to `h` and `k.trans h`.
That theorem pulls stabilizing open subgroups back along the actual
continuous subgroup inclusions and keeps the same local open sets.
Thus no stability premise for either smaller subgroup is added. The imported
smooth constructions derive ambient stable neighbourhoods on all three
original induced spectra.

Let `R : Type u` be any commutative ring. All coefficients range over the
entire original `SmoothRep.{u,u,u} R G`, with their original modules and all
original linear intertwiners. There is no dimension, admissibility or
coefficient-topology restriction. Write `L_X`, `L_Y`, `L_Z` for the existing
full smooth locally constant coefficient sheaf functors and `S_f`, `S_g`,
`S_q` for `SmoothSheafVariation.directImage R` on the original maps.
These direct images take the smooth coreflection of ordinary direct image.
Their coefficient sheaves contain every original locally constant section.

## Actual lax comparison and pullback

For arbitrary original rational arrows `f`, `g`, `q` on locally stable
objects and `e : f ≫ g = q`,
`SmoothSheafVariation.directImageCompMapOfEq R f g q e` is the natural
transformation

```text
S_f ⋙ S_g ⟶ S_q.
```

It is constructed as

```text
directImageCompMap R f g ≫ eqToHom (congrArg (directImage R) e).
```

The first factor is the existing actual lax smooth direct-image comparison.
The second transports its target along equality of the original rational
arrows. This construction neither assumes nor constructs an inverse for the
lax map.

`subgroupRestrictionSmoothDirectImageCompMap h k d R` specializes this map
at `f`, `g`, `q` and their proved subgroup composition equality. Write `C`
for this natural transformation. For every original smooth coefficient `M`,
`subgroupRestrictionSmoothCoefficientMap_comp` proves

```text
b_q(M) =
  b_g(M) ≫ S_g.map(b_f(M)) ≫ C.app(L_X(M)),
```

where `b` denotes the existing full smooth coefficient pullback. The Lean
component statement binds `X`, `Y`, `Z`, `f`, `g`, `q` with `let` and names
the general `directImageCompMapOfEq` explicitly. This is definitionally the
comparison specialized above. The component pullbacks are definitionally the
maps of `InducedRationalSubgroupSmoothTrace`.

`subgroupRestrictionSmoothCoefficientNatTrans_comp` proves the identity
on the entire original coefficient category:

```text
b_q =
  b_g ≫ whiskerRight b_f S_g ≫ whiskerLeft L_X C.
```

It uses the named subgroup comparison and named subgroup coefficient natural
transformations. Both pullback laws and the comparison construction require
no finite-index hypothesis.

## Finite full traces

The trace section assumes only

```text
Finite (V ⧸ W.toSubgroup.subgroupOf V.toSubgroup),
Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup).
```

Each trace theorem introduces the long quotient's finiteness with `letI`,
using the imported `finite_relativeQuotient_trans U V W`. The original
covering and finite literal-fiber conditions for all three arrows are
provided by the existing subgroup geometry. No covering, fiber finiteness,
long quotient finiteness or trace-compatibility premise is added.

For every original coefficient `M`,
`subgroupRestrictionSmoothCoefficientTrace_comp` proves

```text
C.app(L_X(M)) ≫ Tr_q(M) =
  S_g.map(Tr_f(M)) ≫ Tr_g(M).
```

All traces are the existing unnormalized sums over the entire original
fibers of the original maps. Their domains are the actual smooth direct
images, and their targets are the full original coefficient sheaves.
The component statement uses explicit original-object and arrow `let`
bindings, finite-fiber `letI` witnesses and the general equality-transported
comparison. Its trace maps are definitionally the subgroup smooth traces
constructed in `InducedRationalSubgroupSmoothTrace`.

`subgroupRestrictionSmoothCoefficientTraceNatTrans_comp` proves

```text
whiskerLeft L_X C ≫ Tr_q =
  whiskerRight Tr_f S_g ≫ Tr_g.
```

It uses the named subgroup comparison and subgroup trace natural
transformations, retaining every original smooth coefficient intertwiner.
The lax comparison is on the left of the long trace, with no assertion that
the long trace factors through an inverse comparison.

## Provenance and implemented proofs

The provenance is internal: this construction specializes
`InducedRationalSubgroupSmoothTrace`, `InducedRationalSubgroupTransitivity`
and `InducedRationalSmoothSheafTrace`. The generic equality-transported
comparison composes the actual existing lax map with equality transport.
The private component pullback and trace lemmas substitute `q` using `e` and
reduce to the existing generic rational smooth composition laws. The private
pullback natural-transformation law follows componentwise; the trace law
transports the existing rational trace natural-transformation law by the same
substitution. The four subgroup laws apply those helpers to the proved
original subgroup composition equality.

The stability witnesses, covering predicates, finite fibers and long relative
quotient finiteness are derived as described above. All new intrinsic laws
are proved. No external Harris or Berkovich assertion is introduced.

This is fixed-rational-presentation subgroup transitivity for ordinary-open
degree-zero smooth coefficient sheaves, under the explicit original
largest-subgroup local stability premise. General rational coverings,
analytic and etale realization, Godement and higher derived traces,
geometric compact-support comparison, arithmetic Hecke identification,
Shimura specialization and Harris compatibility remain obligations of the
broader task.
