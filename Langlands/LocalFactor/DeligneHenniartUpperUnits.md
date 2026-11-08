# Upper ramification groups of the local Weil group and unit levels

Supporting lemmas for DH81 4.3–4.6 (Deligne–Henniart 1981). They relate the
actual upper ramification groups `upperGroup F s` of the local Weil group to
the unit filtration of `F` through a Weil reciprocity candidate.

- `candidateGaloisHom_reciprocityUnits`: for a candidate
  `e : RankOne.ReciprocityCandidate F` and a local Weil element `w`, the
  candidate's Galois map applied to `RankOne.reciprocityUnits F e w` is the
  image of `localProjection F w` in the Galois abelianization. The proof
  unfolds both maps and cancels `e.symm (e x) = x`.
- `absoluteInertia_le_range_localProjection`: every element of the absolute
  inertia group (canonical topological data) is the Galois projection of a
  local Weil element, namely its degree-zero inclusion `localInertiaInclusion`.
- `upperGroup_map_reciprocityUnits`: let `e` satisfy
  `GeometricWeilReciprocityRelation` for the canonical topological data, and
  let `s ≥ 0`. Then `RankOne.reciprocityUnits F e` maps `upperGroup F s` onto
  `T.unitFiltration ⌈s⌉₊`, where `T = F.canonicalTopologicalData`. This is the
  Weil-group form of the upper-numbering theorem of local class field theory
  (Serre, *Local Fields*, XV §2, Corollary 3 to Theorem 1).

Two unproved published propositions are explicit hypotheses:
`AbsoluteReciprocityRealUnitImages` (the third clause of
`AbsoluteUpperReciprocityTheorems`) and
`AbsoluteUpperInertia F F.canonicalTopologicalData`. Injectivity of the
reciprocity map comes from the published theorem
`profiniteReciprocityCompletion`.

Proof of the main lemma. Write `r` for the candidate's Galois map. The first
hypothesis says that `r` maps `T.unitFiltration ⌈s⌉₊` onto the abelianized
upper group `localAbelianUpperRamificationGroup F s`.
- Forward inclusion: for `w` in `upperGroup F s`, the first lemma puts
  `r (reciprocityUnits w)` in the abelianized upper group. So it equals `r u`
  for a unit `u` of level `⌈s⌉₊`, and injectivity gives `u = reciprocityUnits w`.
- Reverse inclusion: for `u` of level `⌈s⌉₊`, `r u` is the image of some `σ`
  in the absolute upper group of index `s`. By antitonicity and the inertia
  hypothesis, `σ` lies in absolute inertia, so `σ = localProjection w` for some
  `w`, and that `w` lies in `upperGroup F s`. Then
  `r (reciprocityUnits w) = r u`, and injectivity gives
  `reciprocityUnits w = u`.

## The base component of a common-closure family

The target statement `VirtualStabilityStatement` reads quasicharacters of `F`
through the base component `reciprocityUnits F eC (baseExtension F)` of a
common-closure reciprocity family `eC`, on the bottom Weil subgroup
`weilSubgroup F (baseExtension F)`. This component takes values in the units
of the bottom intermediate field, not in `F.Carrierˣ`. The next lemmas move
the main lemma to that setting.

- `baseFieldUnitsEquiv_reciprocityUnits`: after the bottom-field unit
  equivalence `Correspondence.baseFieldUnitsEquiv F`, the base component
  applied to `g` equals `RankOne.reciprocityUnits F e g.val`, where
  `e = Correspondence.baseReciprocityCandidate F eC`. This is the unit clause
  of the published `Correspondence.baseReciprocityCandidate_spec`.
- `mem_basePrincipalUnits_iff`: for each `n`, the bottom-field unit
  equivalence preserves and reflects principal units of level `n`. Here the
  principal units are those of `F.canonicalTopologicalData` and of
  `fieldData F (baseExtension F)`. This is the published
  `PadicField.ConductorTransport.mem_principalUnits_map_iff`, applied to the
  p-adic equivalence `Correspondence.baseFieldPadicEquiv F`.
- `geometric_baseReciprocityCandidate`: if `CommonClosureGeometricStatement`
  holds and `eC` is normalized (`NormalizedReciprocity F eC`), then the
  transported base candidate satisfies `GeometricWeilReciprocityRelation` for
  the canonical topological data. This is clause (1) of that statement,
  applied to `baseReciprocityCandidate_spec`. `CommonClosureGeometricStatement`
  is published and unproved, so it is an explicit hypothesis.
- `baseUpperGroup F s` (definition): the upper ramification group
  `upperGroup F s` of the local Weil group viewed in the bottom Weil subgroup,
  that is, its pullback `(upperGroup F s).comap (baseWeilInclusion F)` under
  the literal inclusion. `mem_baseUpperGroup` says that `g` lies in it exactly
  when `g.val` lies in `upperGroup F s`; this holds by definition. Since the
  bottom Weil subgroup is the whole group, this is only a change of ambient
  group. It is an internal definition with no separate literature source.
- `baseUpperGroup_map_reciprocityUnits`: let the transported base candidate be
  geometric and let `s ≥ 0`. Then the base component maps
  `baseUpperGroup F s` onto
  `(fieldData F (baseExtension F)).principalUnits ⌈s⌉₊`.
  Besides the two hypotheses of the main lemma, it assumes the published,
  unproved `UnitFiltrationComparison`. That statement identifies
  `T.unitFiltration n` with the valuation principal units `T.principalUnits n`.

Proof of `baseUpperGroup_map_reciprocityUnits`. Apply the main lemma to the
transported base candidate and rewrite its right side with
`UnitFiltrationComparison`. This gives `F.canonicalTopologicalData.principalUnits ⌈s⌉₊`.
- Forward inclusion: by the second lemma, it suffices that
  `baseFieldUnitsEquiv` sends the image of `g` to a unit of level `⌈s⌉₊` of `F`.
  By the first lemma this image is `RankOne.reciprocityUnits F e g.val`, which
  lies in the image of `upperGroup F s`.
- Reverse inclusion: a unit `u` of level `⌈s⌉₊` of the bottom field is sent to
  a unit of level `⌈s⌉₊` of `F`. That unit is `RankOne.reciprocityUnits F e w`
  for some `w` in `upperGroup F s`. The bottom Weil subgroup is the whole
  group (`baseWeil_eq_top`), so `w` gives an element of it. By the first lemma
  the bottom-field equivalence sends its image to the same unit as `u`.
  Injectivity of the equivalence then finishes the proof.

The proof declares the bottom-field and base topologies locally. The
bottom-field equivalence is a topological group isomorphism, and the
Library's own instances for it are file-local.
