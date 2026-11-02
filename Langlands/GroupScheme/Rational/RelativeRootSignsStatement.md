# Relative-root signs determine the dynamic subgroup functors

Author: Worker 1269.

`Langlands.GroupScheme.RelativeRootSignsDetermineDynamicStatement` is an
unproved proposition target. It quantifies over every field `k : Type u`,
connected reductive group scheme `G` over `Spec k`, maximal split torus
inclusion `i : T.toGrp ⟶ G`, and two cocharacters `zeta` and `eta` of `T`.
For every actual root `α ∈ relativeRoots i`, its antecedent requires the
following three equivalences:

- `0 ≤ ⟨α,zeta⟩ ↔ 0 ≤ ⟨α,eta⟩`;
- `⟨α,zeta⟩ = 0 ↔ ⟨α,eta⟩ = 0`;
- `0 < ⟨α,zeta⟩ ↔ 0 < ⟨α,eta⟩`.

Here the integer pairing is the published `latticePairing T`. The conclusion
identifies `Dynamic.parabolic`, `Dynamic.centralizer`, and
`Dynamic.unipotent` for the two composed cocharacters
`CommGroupScheme.groupHom zeta ≫ i` and
`CommGroupScheme.groupHom eta ≫ i`.
These are equalities of the published `SubgroupFunctor G` objects, hence
equalities on every scheme over `Spec k`.

The target uses the explicit sign formula because
`HaveSameRelativeRootSigns` is not in the Library base used for this
submission. It introduces no replacement sign predicate. It imposes no
genericity, standard-subset presentation, root-system premise, or dynamic
subgroup realization premise. Arbitrary characteristic, imperfect fields,
nonsplit groups, nonreduced relative-root systems, and the empty root set
remain included.

## Sources and derived provenance

- Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
  §2.11, Propositions 2.11.1–2.11.3, printed pp.130–131
  (PDF pp.161–162). These give the dynamic functors, their closed
  representatives, connectedness, smoothness, and the Lie spaces selected
  by nonnegative, zero, and positive cocharacter weights.
- Conrad, Gabber and Prasad, *Pseudo-reductive Groups*, second edition
  (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`,
  Proposition 3.3.6 and its proof, printed pp.109–110 (PDF pp.135–136).
  For a split torus acting on a smooth affine group over any field, a
  subsemigroup of characters determines the unique smooth connected stable
  subgroup with Lie algebra equal to the sum of all ambient weight spaces
  in that semigroup.
- Kaletha and Prasad, *Corrections and Additions* (2024), source
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  PDF p.25, Section 2.11. The listed dynamic-method corrections concern
  notation and leave these hypotheses and conclusions unchanged.

The sign implication is a derived combination of these results. The split
torus preserves each dynamic subgroup because its image commutes with the
cocharacter. The dynamic Lie formulas select the ambient torus weight spaces
according to their integer pairings. The nonzero weights with nonzero weight
spaces are exactly `relativeRoots i`; the zero character has the same pairing
with both cocharacters automatically. Consequently, sign agreement selects
the same full weight spaces. Apply the uniqueness of Proposition 3.3.6 for
the nonnegative, zero, and positive character semigroups to identify the
represented subgroups, then their subgroup functors.

This paragraph records the source route for the target. The module defines
the proposition and supplies no proof of that route or of the proposition.
