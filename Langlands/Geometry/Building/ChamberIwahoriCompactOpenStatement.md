# Compact openness of the actual chamber Iwahori

This file defines the proposition
`Langlands.Geometry.Building.ParahoricBuildingData.ChamberIwahoriCompactOpenStatement`.
It states that the actual chamber subgroup `I_C = P_C` is compact and open
in the canonical topology on `G(F)`, conditional on the specified actual
apartment data and axioms. It supplies a statement target, not a proof.

## Sources and derived provenance

The registered original sources are:

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  The source route uses Fact 2.2.3 and Remark 2.2.2, printed p. 70 /
  PDF p. 101; the Chapter 7 opening, printed pp. 235–236 /
  PDF pp. 266–267; Definition 7.3.3(3) and Example 7.3.7(1),
  printed p. 247 / PDF p. 278; Corollary 7.3.14, printed pp. 251–252 /
  PDF pp. 282–283; Definition 7.4.1(4), Lemma 7.4.4 and
  Definition 7.4.5(2), printed pp. 255–256 / PDF pp. 286–287.
- Kaletha–Prasad, *Corrections and additions to Bruhat–Tits theory:
  a new approach*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
  PDF p. 24 adds Henselianity to the standing assumptions of §2.2;
  PDF p. 33 adds AS 5 to the Chapter 7 ambient assumptions;
  PDF p. 35 corrects the singleton notation in 7.4.1 and the function
  subscript in the proof of Lemma 7.4.4.

The compact-open assertion is a derived local-field consequence of these
passages. For a chamber `C`, choose `x ∈ C`. Lemma 7.4.4 identifies
`P_C` with `P_x`. The constant zero function is concave by
Example 7.3.7(1), and Definition 7.3.3(3) identifies its full subgroup
with `P_x`. Corollary 7.3.14 states that this full subgroup is bounded
and open, since the zero function has no infinite values. An open subgroup
of the analytic topological group `G(F)` is closed. Fact 2.2.3 then
identifies its algebraic boundedness with compactness for locally compact
`F`. Remark 2.2.2 describes the analytic topology using a closed affine
embedding; the named rational-point topology used here is its regular-function
evaluation formulation.

This paragraph records the mathematical derivation of the target. It does
not claim that the intermediate boundedness, topology comparison, facet
constancy or compactness arguments have been proved in Lean by this file.
In particular, no previously published compactness *statement* is treated
as an available proof.

## Actual data and exact hypotheses

The parameters are a field `F` with `ValuativeRel F`, its topology, an
`IsNonarchimedeanLocalField F` instance, an affine `F`-group scheme `G`,
and `P : ParahoricBuildingData G`. The local-field class covers both
characteristics and provides the compatible discrete valuation topology
and local compactness. In this scope the valuation is Henselian, as required
by the corrected §2.2 and Chapter 7 assumptions.

The inherited `ValuationBuildingData` supplies connected reductivity and
finite type, an actual maximal split torus `i : S → G`, its root-valuation
apartment and normalizer action, and the represented centralizer of this
same torus. The inherited `ZeroSubgroupDatum` defines the actual central
subgroup `Z(F)^0` through the shared construction. Thus `chamberIwahori C`
is the existing `P.parahoric C`, defined from that central subgroup and
the actual sharp root-generated subgroup. It is not a freely chosen
compact open subgroup.

The explicit premise
`P.apartment.SatisfiesApartmentAxioms P.centralizer` retains full V 6,
V 7 and the fixed-apartment AS 2–AS 5 conditions, including the corrected
AS 5 premise and the rank-zero case. These conditions are used in the
conditional Chapter 7 scope. This predicate is not a certificate of all
building axioms or of the existence of such data for every reductive group.
There is no assumption of bounded open stabilizers, compact openness of
`P_C`, or the conclusion of the boundedness–compactness comparison.

The only geometric input to this conclusion is
`AffineRootSystem.IsChamber P.affineRoots C`. This predicate includes
nonemptiness. No point, generic cocharacter or minimal-parabolic choice
is needed in the compactness conclusion; those choices occur in the
separate decomposition targets on the same actual data. No split,
quasi-split, tameness, characteristic-zero or large-residue-characteristic
restriction is imposed.

## Lean statement and topology

The declaration installs `IsAffine G.X.left` from the existing affine
structure morphism, then installs precisely
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`
on `rationalPoints G`. For every actual apartment chamber `C`, its
conclusion is the conjunction

```text
IsCompact (P.chamberIwahori C : Set (rationalPoints G)) ∧
IsOpen (P.chamberIwahori C : Set (rationalPoints G)).
```

The topology is fixed by the algebraic group and the given local field;
it is not an arbitrary topology parameter on `G(F)`. Compactness and
openness concern the ambient subset, not a newly bundled topological
subgroup.

This target concerns the full chamber parahoric with its `Z(F)^0`
factor. It does not identify that subgroup with the sharp chamber
subgroup. It is also distinct from Renard V.5.2's smaller simultaneous
normal compact-open bases. Full chamber and facet factor bijections
are stated in `ChamberIwahoriStatement`; they are not proved here.
