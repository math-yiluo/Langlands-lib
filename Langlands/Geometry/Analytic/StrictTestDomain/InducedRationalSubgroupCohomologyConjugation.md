# Conjugation of the original compact cohomology towers

This internal construction extends the existing geometric conjugation of the
original finite-index rational subgroup tower to its full compact-function,
Godement, cohomology and degree-zero sheaf-derived coefficient diagrams.
The construction derives stability at the conjugate domain from the original
largest-level premise. All maps are the existing proper pullbacks along the
original rational translations; the comparisons are proved from the naturality
of the existing spatial diagrams.

## Inputs and scope

The complete ultrametric normed field `K`, presented strict affinoid algebra
`P`, and topological group `G` share arbitrary universe `u`. Assume
`IsTopologicalGroup G`, an actual rational spectral action `ρ`, an open
subgroup `U`, an originally `U`-invariant rational presentation `d`, and
`g : G`. The sole stability premise is `HasStableNeighbourhoods` for the
original local spectrum at `U`, with its original subgroup action.

The coefficient ring is any commutative ring `R : Type u`. The diagrams use
the entire original `SmoothRep.{u, u, u} R G` and all its intertwiners. No
finite-dimensionality, admissibility, or coefficient-topology premise is
added. Every original finite-index open subgroup below `U` is retained;
normality is unnecessary.

Write `dᵍ` for the original moved presentation
`(ρ.invariantConjugationEquivalence U g).functor.obj d`, and `E` for
`conjugationEquivalence U g`. These are explanatory names only. The actual
target levels are the original conjugate open subgroups `g V g⁻¹`.
The underlying spaces are the existing balanced induced spectra, with their
actual quotient topology and full continuous `G` action.

## Stability and the smooth proper tower

The private `stableNeighbourhoods_of_equivariantHomeomorph` transports stable
neighbourhoods along an actual equivariant homeomorphism. Given a target
point and open neighbourhood, pull them back, choose a source stable open
neighbourhood, and take its image under the homeomorphism. Openness,
containment, and stability under the same open subgroup follow directly.

`hasStableNeighbourhoods_conjugate_local` first derives full-group stability
of the original induced spectrum at `base U`. It transports this property
along `inducedConjugationHomeomorph d g (base U)`, which is equivariant for
every element of the original `G`. The existing
`SpatialSheaves.hasStableNeighbourhoods_iff` then recovers local subgroup
stability for `dᵍ`. Thus the moved local stability is a consequence of the
original premise, rather than a second assumption. Local instances derive
induced stability at every source and conjugate level as needed.

`smoothConjugationIso d g V` lifts the original
`rationalConjugationIso d g V` to `SmoothProperTransport ρ`.
Its hom and inverse are precisely the original rational translations,
with properness already derived from their actual quotient homeomorphism.
The faithful forgetful functor reflects their two inverse identities.
The transport equalities for both maps are definitional.

`smoothTowerConjugationIso` assembles these components into

```text
smoothTower d ≅ E.functor ⋙ smoothTower dᵍ.
```

Its naturality square is exactly the original rational conjugation square
with every original subgroup arrow, reflected through faithful forgetting.

## Full coefficient towers and original maps

For each existing contravariant spatial diagram `F`, the construction uses

```text
Functor.isoWhiskerRight (NatIso.op (smoothTowerConjugationIso d g)) F.
```

The opposite natural isomorphism reverses the direction. Consequently each
constructed coefficient isomorphism has source the moved tower reindexed
along `E.functor.op`, and target the original tower. Both its level
naturality and its coefficient naturality are retained.

| Declaration | Existing diagram transported |
| --- | --- |
| `compactFunctionsTowerConjugationIso` | All compactly supported locally constant coefficient functions |
| `invariantCompactFunctionsTowerConjugationIso` | Whole-group invariants of those functions |
| `godementCompactTowerConjugationIso` | Actual compact smooth Godement cochain complexes |
| `godementInvariantCompactTowerConjugationIso` | The same complexes with termwise whole-group invariants |
| `godementCohomologyTowerConjugationIso q` | Actual smooth-representation homology in degree `q` |
| `godementInvariantCohomologyTowerConjugationIso q` | Module homology after termwise invariants |
| `godementInvariantsArrowTowerConjugationIso q` | The original invariants edge and its original squares in the arrow category |
| `compactDerivedZeroTowerConjugationIso` | Existing sheaf-derived compact sections and proper maps in degree zero |
| `invariantCompactDerivedZeroTowerConjugationIso` | Their whole-group invariant degree-zero counterpart |

The `_hom_app` theorems identify all nine forward components with the
corresponding original proper pullback natural transformations.
For compact functions, `_inv_app` also identifies the inverse component
with pullback along the original inverse rational translation. These are
definitional identifications; the full coefficient maps are preserved.
The chain and homology identifications retain the actual sheaf coefficient
map followed by spatial pullback, and homology of that same chain map.

`compactFunctionsTowerConjugationIso_apply` proves that an original compact
function `s` is pulled back by composition with
`inducedConjugationHomeomorph d g V`. Its value at an original induced point
`z` is `s(e(z))`. The representative theorem `_apply_mk` gives

```text
(pullback s)([a,x]) = s([a*g⁻¹, localSpectrumMap(x)]).
```

Here `localSpectrumMap` is the original bounded rational pullback's map on
spectra. The inverse-label correction and the original coefficient value
are retained. Compact support is preserved using the proved properness;
there is no replacement support or coefficient representation.

## Compatibility with invariant and degree-zero comparisons

`godementInvariantCompactTowerConjugationIso_comparison` proves that
conjugation commutes with the existing comparison from degreewise
invariants of the compact smooth Godement complex to the constructed
invariant compact complex. `godementInvariantsEdgeTower_conjugation`
proves the corresponding square for the canonical invariants edge in
every degree. These are equalities of natural transformations of whole
coefficient towers.

The edge square requires no preservation-of-homology premise.
The existing edge is an isomorphism in degree zero. Its isomorphism
property in every degree still requires that `smoothInvariants R G`
preserves homology. The conjugation isomorphism in the arrow category
retains each edge as an arrow; it does not assert that the edge itself is
always invertible.

Four `_conjugation` theorems prove compatibility with the existing
degree-zero identifications with original compact functions: the Godement
and sheaf-derived routes, each with and without whole-group invariants.
The final two `_conjugation` theorems prove compatibility with
`godementDerivedZeroTowerIso` and
`godementInvariantDerivedZeroTowerIso`, which compare the two routes
through those same original functions.

Each square follows by extensionality in the original level and the
naturality of the corresponding spatial natural transformation evaluated
at `(smoothConjugationIso d g V).hom.op`. The implementation does not
assume any of these squares as extra data. Both routes therefore preserve
the previously proved compact-function identifications.

## Provenance and remaining obligations

The provenance is internal. The construction reuses the existing original
rational conjugation maps, quotient homeomorphisms, local/induced stability
equivalence, smooth proper transport category, and full coefficient
diagrams by Lean name. The new ingredients are the elementary equivariant
transport of stable neighbourhoods, the faithful lift, contravariant
whiskering, and the resulting naturality squares. No external source
assertion is invoked for this unit.

The Godement cohomology towers have all degrees, while the sheaf-derived
spatial diagrams used here have only degree zero. This construction does
not identify Godement homology with sheaf-derived cohomology in positive
degree. Godement acyclicity or resolution exactness, higher sheaf-derived
spatial maps and traces, conjugation compatibility of covariant traces,
general rational coverings and charts, analytic or etale realization,
arithmetic Hecke identification and convolution, uniformization, Shimura
specialization and Harris compatibility remain obligations of the broader
framework.
