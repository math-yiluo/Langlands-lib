# Herbrand's quotient theorem for actual finite p-adic Galois extensions

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`
(namespace `Langlands.Ramification.HerbrandBridge`).

## What the module proves

Let `K` and `L` be actual `PadicField`s with `L/K` Galois. Write `G = Gal(L/K)`. Let
`T : L.TopologicalData` be any realization of `L`. Write `E_H` for the actual fixed field
`IntermediateField.fixedField H` of a subgroup `H`. The module proves three of the
Library propositions of `Langlands.LocalFactor.Ramification.Herbrand.ArithmeticStatement`
for every such `K`, `L` and `T`. It adds no hypotheses:

- `upperQuotientCompatibility K L T : Padic.UpperQuotientCompatibility K L T`. For every
  normal `H`, every realization `S` of `fixedPadicField K L H`, and every `v ≥ -1`, the
  image of `G^v` under `AlgEquiv.restrictNormalHom` to `E_H` is the upper group of
  `E_H/K` at `v`. This is Serre, *Local Fields*, IV.3, Proposition 14.
- `herbrandNormalSubgroup K L T : Padic.HerbrandNormalSubgroup K L T`. For every
  normal `H`, every `S`, and every `u ≥ -1`, the image of `G_u` under the same restriction
  is the lower group of `E_H/K` at `φ_{L/E_H}(u)`. This is Serre IV.3, Lemma 5
  (Herbrand's theorem).
- `lowerSubgroupCompatibility K L T : Padic.LowerSubgroupCompatibility K L T`. For every
  subgroup `H`, normal or not, and every `u ≥ -1`, the image of the lower group of
  `L/E_H` under `AlgEquiv.restrictScalarsHom K.Carrier` is `G_u ⊓ H`. This is Serre IV.1,
  Proposition 2, with real indices by the ceiling convention.

It also proves the phi tower law through the actual fixed field of a normal subgroup:

- `herbrandPhi_fixedField_tower K L T H S u`: for every real `u`,
  `φ_{L/K}(u) = φ_{E_H/K}(φ_{L/E_H}(u))`. Here `φ_{L/K} = Padic.herbrandPhi T K.Carrier`,
  `φ_{L/E_H} = Padic.herbrandPhi T (fixedField H)` and
  `φ_{E_H/K} = Padic.herbrandPhi S K.Carrier`. This is the first formula of Serre IV.3,
  Proposition 15, for the tower `K ⊆ E_H ⊆ L`. The Library propositions
  `HerbrandPhiTower`, `HerbrandPsiTower` and `UpperRestrictionCompatibility` concern an
  independently presented intermediate field `E`. They are not proved here.

The named definition is `fixedSubringEquiv K L T H S`. It is the ring isomorphism from
the fixed subring `FixedPoints.subring T.Integers H` of the supplied integer ring of `L`
to the supplied integer ring `S.Integers` of `E_H`. It is the identity on underlying
elements of `L`. `fixedSubringEquiv_coe` records this by `rfl`. The relevant `G`-action
on `T.Integers` is `Padic.integerAction T K.Carrier`.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Used:
  Chapter IV, §1, Proposition 2 (printed p. 62), and §3, Lemma 5 and Propositions 14–15
  (printed pp. 73–75). The Library statement module cites the same places.
- The proofs use the ported Anthropic FLT theorems in `Langlands.AnthropicFLT` (accepted
  candidate `cf07dc37-888b-4c8a-8bc0-81226d21710e`). They are Herbrand's theorem in
  lower numbering for a finite group acting faithfully on a discrete valuation ring with
  separable residue extension
  (`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`),
  and its consequences for `φ`
  (`IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq`)
  and for upper numbering
  (`IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`).
  Both of these are stated at nonnegative rational arguments.

All other declarations are internal transport lemmas between the two formalizations. The
Library side has real-indexed groups built from `Padic.integerAction`. The source side has
rational-indexed groups of `IsLocalRing.lowerRamificationGroup`.

## Proof (as implemented)

1. **Transport** (section `Transport`). Let `e : A ≃+* B` be a ring isomorphism of local
   rings and `f : G ≃* G'` a group isomorphism. Suppose `e (g • a) = f g • e a`. Then
   `f` maps `IsLocalRing.lowerRamificationGroup A G i` onto
   `IsLocalRing.lowerRamificationGroup B G' i`
   (`map_lowerRamificationGroup_of_equivariant`), and so the cardinalities agree
   (`lowerRamificationCard_of_equivariant`). The proof uses that `e` maps
   `maximalIdeal A ^ n` onto `maximalIdeal B ^ n` (`ringEquiv_mem_maximalIdeal_pow_iff`).
2. **Library φ at rational points** (section `Phi`). Suppose the Library orders
   `Padic.lowerGroupOrder T K i` equal the source cardinalities
   `IsLocalRing.lowerRamificationCard A Γ i` for all `i`. Then, for every rational `u ≥ 0`,
   the Library real `herbrandPhi` at `u` is the cast of the source rational
   `herbrandPhi` at `u` (`herbrandPhi_ratCast`). Both are given by the floor formula
   (`Padic.herbrandPhi_floor`, `IsLocalRing.herbrandPhi_of_pos`). For finite `Γ`, the
   ceiling of the Library `ψ` at a rational `w ≥ 0` is the source index
   `upperRamificationIndex A Γ w` (`ceil_herbrandPsi_ratCast`). Hence the Library upper
   group at `w` is the Library lower group with that index
   (`upperRamificationGroup_ratCast`). The Library `φ` takes rational values at natural
   numbers (`herbrandPhi_natCast_rat`). The Library upper group is constant for `w`
   between `v` and `φ(⌈ψ(v)⌉)` (`upperRamificationGroup_eq_of_le`). So for every
   `v > -1` there is a rational `q ≥ 0` with `v ≤ q` such that `G^w = G^v` for all `w`
   with `v ≤ w ≤ q` (`exists_rat_upperRamificationGroup_eq`).
3. **Source hypotheses** (sections `Source`, `Galois`). The Library lower groups of `T`
   over `K` are, by definition, the source lower groups of `T.Integers` under
   `Padic.integerAction` (`lowerRamificationGroup_eq_source`, `lowerGroupOrder_eq_source`,
   both `rfl`). The action is faithful (`integerAction_faithful`, by fraction-ring
   extensionality). `T.Integers` is a discrete valuation ring with finite residue field.
   The residue field of the fixed subring embeds into it and so is finite, which gives
   separability. With these, `source_map_lowerRamificationGroup_mk` is the ported
   Herbrand theorem for `T.Integers`, `G` and normal `H`.
4. **Fixed fields.** By `PadicField.TopologicalData.relative_mem_integers_iff`, an element
   of `E_H` lies in `S.Integers` exactly when it lies in `T.Integers`. This gives
   `fixedSubringEquiv`. It intertwines the action of `G ⧸ H` on the fixed subring with
   the action of `AlgEquiv.restrictNormalHom E_H g` on `S.Integers`
   (`fixedSubringEquiv_smul`). Through `IsGalois.normalAutEquivQuotient`, step 1 turns
   source statements about `G ⧸ H` into Library statements about `Gal(E_H/K)`. This gives
   `map_restrictNormalHom_eq` (images of lower groups) and
   `lowerGroupOrder_fixedPadicField` (orders). Similarly, the Library orders of `L/E_H`
   are the source orders of `H` (`lowerGroupOrder_fixedField`, via
   `IntermediateField.subgroupEquivAlgEquiv`).
5. **Upper numbering** (`upperQuotientCompatibility`). At `v = -1` both sides are the
   whole group, since `restrictNormalHom` is surjective. For `v > -1`, step 2 gives
   rational `q_T` for `L/K` and `q_S` for `E_H/K`. Let `w = min q_T q_S`. Then `w ≥ 0`, and
   replacing `v` by `w` changes neither upper group. At `w` both upper groups are Library
   lower groups with the source indices (step 2). The ported upper-numbering theorem and
   step 4 then identify them.
6. **φ tower** (`herbrandPhi_fixedField_tower`). For rational `u ≤ 0` all three functions
   are the identity. For rational `u > 0`, step 2 rewrites the three Library functions as
   source functions; the inner value is nonnegative by `Padic.herbrandPhi_pos`. The
   ported φ-transitivity theorem then applies. Both sides are continuous in `u` and agree
   on the dense set of rationals, so they agree everywhere (`Continuous.ext_on`,
   `Rat.denseRange_cast`).
7. **Lower numbering** (`herbrandNormalSubgroup`). `G_u = G^{φ_{L/K}(u)}`
   (`Padic.upperRamificationGroup_phi`), and `φ_{L/K}(u) ≥ -1`. Step 5 maps this onto the
   upper group of `E_H/K` at `φ_{L/K}(u)`. By step 6 this index equals
   `φ_{E_H/K}(φ_{L/E_H}(u))`, and `Padic.upperRamificationGroup_phi` for `S` turns the
   upper group back into the lower group at `φ_{L/E_H}(u)`.
8. **Subgroups** (`lowerSubgroupCompatibility`). The range of
   `AlgEquiv.restrictScalarsHom K.Carrier` on `Gal(L/E_H)` is `H`
   (`range_restrictScalarsHom_fixedField`, from `IntermediateField.fixingSubgroup_fixedField`
   and `IntermediateField.fixingSubgroupEquiv`). At `u = -1` both sides are therefore `H`.
   For `u > -1` with `⌈u⌉ = n`, both real groups are the natural-index groups at `n`
   (`lowerRamificationGroupReal_of_ceil_eq`). An automorphism over `E_H` and its scalar
   restriction act identically on `T.Integers`
   (`restrictScalars_mem_lowerRamificationGroup_iff`, by `Iff.rfl`). So the two
   memberships correspond.

The other declarations are elementary helpers: `sum_Icc_one_eq_sum_range`,
`natFloor_ratCast`, `herbrandPhi_natCast_eq` and `finiteDimensional_carrier`.
