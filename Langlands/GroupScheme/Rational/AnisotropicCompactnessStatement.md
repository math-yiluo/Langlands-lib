# Compact rational points and anisotropy over a nonarchimedean local field

Author: Worker 572.

This module states the local-field compactness consequence of
Kaletha--Prasad Theorem 2.2.9. Both declarations are proposition definitions.
The module supplies no proof of either implication.

## Exact meaning

For an actual field `F : Type u` with `Field F`, `ValuativeRel F`,
`TopologicalSpace F`, and `IsNonarchimedeanLocalField F`, an actual group
scheme `G` over `Spec F`, and `hG : IsConnectedReductive G`,
`AnisotropicCompactness G hG` asserts

```text
IsCompact (Set.univ : Set (rationalPoints G)) ↔ IsAnisotropic G.
```

The definition first obtains `IsAffineHom G.X.hom` from `hG.isAffineHom`
and `IsAffine G.X.left` from `isAffine_of_isAffineHom`. It then explicitly
installs `rationalPointTopology F G.X`. Compactness therefore concerns the
full actual rational-point set with the canonical regular-function evaluation
topology. No freely chosen topology on this point set occurs.

`AnisotropicCompactnessStatement.{u}` universally quantifies these fields,
groups and reductivity witnesses at arbitrary universe `u`. The field
hypotheses impose the compatible nontrivial nonarchimedean valuation topology
and local compactness; there is no characteristic, tameness, splitting, rank
or residue-characteristic restriction.

The imported predicate `IsAnisotropic G` means `splitRank G = 0`.
The imported theorem `isAnisotropic_iff` identifies it with absence of
nontrivial closed split subtori. In particular, central split tori count:
this uses the split-rank-zero convention already fixed in
`Rational.SplitTorus`, under which the multiplicative group is not
anisotropic. It does not use the alternative convention that excludes only
noncentral split tori.

`IsConnectedReductive` retains smoothness, affineness, connectedness and
trivial geometric unipotent radical. The statement assumes no boundedness,
compactness, representation, building datum or model-existence result in
addition to these actual-group hypotheses.

## Original sources and corrections

- Kaletha--Prasad, *Bruhat--Tits Theory: A New Approach* (2023),
  source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Section 2.2, printed p.70 / PDF p.101, fixes a connected reductive
  group. Definition 2.2.1 defines boundedness by all regular functions;
  Remark 2.2.2 gives the affine-coordinate analytic topology; Fact 2.2.3
  compares closed bounded sets with compact sets over a locally compact
  field. Theorem 2.2.9, printed p.71 / PDF p.102, states boundedness of
  `G(k)` exactly for anisotropic `G`. Its immediately following paragraph,
  printed p.72 / PDF p.103, explicitly states compactness exactly for
  anisotropy when the field is locally compact and nondiscrete. The proof
  ends on printed p.73 / PDF p.104.
- Kaletha--Prasad, *Corrections and additions*, version 1 November 2024,
  source `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  PDF pp.24--25: Section 2.2 assumes the field Henselian throughout;
  Lemma 2.2.5 additionally requires either a separable extension or a
  discrete valuation. Nonarchimedean local fields meet the corrected field
  conditions. No scalar-extension boundedness comparison is asserted here.
  The same corrections change character-valuation signs in Sections 2.5
  and 2.6; the present target contains no character-valuation map.

The source's local compactness consequence is the assertion formalized here.
The implementation uses the published actual-group, anisotropy and point
topology interfaces rather than introducing substitute structures.

## Retained proof and consumer obligations

A proof must establish both implications for the exact canonical topology.
The source obtains the compactness implication from its anisotropic
boundedness theorem and the affine boundedness/compactness comparison.
Its converse uses unboundedness of a nontrivial split torus. These are
mathematical proof obligations, not fields of the data or premises of this
statement.

This prerequisite alone establishes no compactness or openness of a
centralizer-zero subgroup, root-generated subgroup or full parahoric.
Applying it to an anisotropic algebraic quotient still requires constructing
that actual quotient, proving its reductivity and anisotropy, and justifying
the rational-point and topology comparisons used by the consumer.
In particular, this statement does not identify a quotient of rational-point
groups with rational points of a scheme quotient. It neither replaces the
full scheme-center quotient compactness target nor proves the chamber
Iwahori compact-openness target.
