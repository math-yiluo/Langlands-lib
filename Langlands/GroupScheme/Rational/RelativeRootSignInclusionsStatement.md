# Actual relative-root signs and dynamic subgroup inclusions

Authors: Workers 1269, 1263 and 1259.

`Langlands.GroupScheme.RelativeRootSignInclusionsStatement` is an unproved
proposition target. For every field `k : Type u`, connected reductive
group scheme `G` over `Spec k`, maximal split torus inclusion
`i : T.toGrp ⟶ G`, and cocharacters `zeta` and `eta` of `T`, it asserts
both of the following comparisons:

- `Dynamic.parabolic (zeta ≫ i) ≤ Dynamic.parabolic (eta ≫ i)` if and only
  if every actual relative root with nonnegative pairing against `zeta`
  has nonnegative pairing against `eta`.
- If every actual relative root with positive pairing against `zeta`
  has positive pairing against `eta`, then
  `Dynamic.unipotent (zeta ≫ i) ≤ Dynamic.unipotent (eta ≫ i)`.

The displayed composites abbreviate the actual Lean composites through
`CommGroupScheme.groupHom`. Pairings use the published integer-valued
`latticePairing T`, and the roots are exactly `relativeRoots i`.
The order on `SubgroupFunctor G` is inclusion at every test scheme over
`Spec k`. The parabolic comparison is an equivalence; the unipotent
comparison is the stated implication.

These comparisons use arbitrary cocharacters, without a genericity or
standard-subset condition. They retain arbitrary characteristic, imperfect
fields, nonsplit groups, nonreduced relative-root systems, and the empty
root set. No root-system or subgroup realization conclusion is assumed.
The target was formulated with Workers 1263 and 1259 for use by the
standard-subgroup order comparisons.

## Sources and derived provenance

- Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
  §2.11, Propositions 2.11.1–2.11.3, printed pp.130–131
  (PDF pp.161–162). The dynamic subgroups have closed representatives
  that are smooth and connected in this setting. Their Lie algebras
  select the nonnegative and positive cocharacter weight spaces,
  respectively.
- Conrad, Gabber and Prasad, *Pseudo-reductive Groups*, second edition
  (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
  Proposition 3.3.6, printed pp.109–110 (PDF pp.135–136), including
  its maximality assertion. A smooth connected stable subgroup whose
  Lie weights lie in a character subsemigroup lies in the subgroup
  associated with that semigroup.
- Kaletha and Prasad, *Corrections and Additions* (2024), source
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  PDF p.25, Section 2.11 notation corrections.

The source route for sufficiency is the semigroup maximality assertion
applied to the nonnegative or positive pairing semigroup of `eta`.
The image of the split torus preserves the dynamic subgroups of `zeta`.
Its nonzero ambient Lie weights are the actual relative roots; the zero
character is automatically allowed in both nonnegative semigroups and
excluded from both positive ones. The assumed root-sign support
containment therefore gives the required support containment for the
whole Lie algebra.

For necessity in the parabolic equivalence, inclusion of the represented
closed subgroups induces inclusion of their Lie algebras inside `Lie(G)`.
Every actual relative root has a nonzero weight space, and the dynamic
Lie-weight formulas then force each nonnegative `zeta`-root to be
nonnegative for `eta`.

This is a derived formulation of those source results. The module defines
the target and proves neither the comparisons nor their structural inputs.
