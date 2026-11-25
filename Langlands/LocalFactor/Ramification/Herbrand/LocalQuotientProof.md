# Herbrand's quotient theorem for finite Galois extensions over a general base

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.LocalQuotientProof`
(main theorems in namespace `Langlands.Ramification.Local`; helpers in
`Langlands.Ramification.Local.QuotientBridge`).

## What the module proves

The base `K₀` carries only `[Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]`.
Let `K` and `L` be fields with `[Algebra K₀ K] [Algebra K₀ L] [FiniteDimensional K₀ L]
[Algebra K L] [IsScalarTower K₀ K L] [IsGalois K L]`, in independent universes `u₀`, `uK`,
`uL`. Let `T : LocalField.TopologicalData K₀ L` be any realization of `L`. Write
`G = Gal(L/K)` and `E_H` for the actual fixed field `IntermediateField.fixedField H` of a
subgroup `H`. The objects `G_u`, `G^v`, `φ` and `ψ` are those of
`Herbrand.GeneralFinite`, built from `T.Integers`. No characteristic
hypothesis occurs, and `K₀` is not assumed to be a local field. The module proves three
propositions of `Langlands.LocalFactor.Ramification.Herbrand.LocalArithmeticStatement`
for every such `K₀`, `K`, `L` and `T`, with no further hypotheses:

- `upperQuotientCompatibility K L T : UpperQuotientCompatibility K L T`.
  For every normal `H`, every realization `S : LocalField.TopologicalData K₀ E_H` and every
  real `v ≥ -1`, the image of `G^v = upperRamificationGroup T K v` under
  `AlgEquiv.restrictNormalHom E_H` is `upperRamificationGroup S K v`. This is Serre,
  *Local Fields*, IV §3, Proposition 14.
- `herbrandNormalSubgroup K L T : HerbrandNormalSubgroup K L T`. For every normal `H`, every
  `S` and every real `u ≥ -1`, the image of `G_u = lowerRamificationGroupReal T K u` under
  the same restriction is `lowerRamificationGroupReal S K (herbrandPhi T E_H u)`. This is
  Serre IV §3, Lemma 5 (Herbrand's theorem).
- `lowerSubgroupCompatibility K L T : LowerSubgroupCompatibility K L T`. For every subgroup
  `H`, normal or not, and every real `u ≥ -1`, the image of
  `lowerRamificationGroupReal T E_H u` under `AlgEquiv.restrictScalarsHom K` is `G_u ⊓ H`.
  This is Serre IV §1, Proposition 2, with real indices by the ceiling convention. The
  published definition does not bind `[FiniteDimensional K₀ L]`, but this theorem keeps that
  binder. It is used to obtain `FiniteDimensional K L`.

The three theorems take exactly the binder list above. Each concludes the
published proposition unchanged.

It also proves the phi tower law through the actual fixed field of a normal subgroup, as a
public theorem for a finite tower proof:

- `herbrandPhi_fixedField_tower K L T H S u`: for normal `H`, every realization `S` of
  `E_H` and every real `u`, `herbrandPhi T K u = herbrandPhi S K (herbrandPhi T E_H u)`,
  that is `φ_{L/K} = φ_{E_H/K} ∘ φ_{L/E_H}`. This is the first formula of Serre IV §3,
  Proposition 15, for the tower `K ⊆ E_H ⊆ L`. The Library propositions
  `HerbrandPhiTower`, `HerbrandPsiTower` and `UpperRestrictionCompatibility` concern an
  independently presented intermediate field `E`. They are not proved here.

The only definition is `QuotientBridge.fixedSubringEquiv K L T H S`. It is the ring
isomorphism from the fixed subring `FixedPoints.subring T.Integers H` of the supplied
integer ring of `L` to the supplied integer ring `S.Integers` of `E_H`. It is the identity
on underlying elements of `L`, which `fixedSubringEquiv_coe` records by `rfl`. Throughout,
`G` acts on `T.Integers` by `integerAction T K` of `Ramification/LocalGalois.lean`.

## Sources

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979). Registered as
  `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Used: Chapter IV,
  §1, Proposition 2 (printed p. 62), and §3, Propositions 14–15 (printed p. 74) and Lemma 5
  (printed p. 75). The statement module `Herbrand/LocalArithmeticStatement` cites the same
  places. Serre works over complete discretely valued fields with separable residue
  extensions, so both characteristics are covered.
- The proofs use the ported Anthropic FLT theorems in `Langlands.AnthropicFLT`, imported
  through `Herbrand.QuotientProof`. The first is Herbrand's theorem in lower numbering for a
  finite group acting faithfully on a discrete valuation ring with separable residue
  extension
  (`Langlands.Ramification.map_lowerGroup_mk_eq_of_isSeparable_residueField`).
  Its consequences are used for `φ`
  (`Langlands.Ramification.herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq`)
  and for upper numbering
  (`Langlands.Ramification.upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq`). Both
  consequences are stated at nonnegative rational arguments.
- The structure of the proof follows the published p-adic proof
  `Herbrand/QuotientProof.lean` (namespace `Langlands.Ramification.HerbrandBridge`). That
  proof states the same three results for `K₀ = Padic p`. Its general transport lemmas are
  imported and used directly: `HerbrandBridge.map_lowerRamificationGroup_of_equivariant`,
  `HerbrandBridge.lowerRamificationCard_of_equivariant`,
  `HerbrandBridge.sum_Icc_one_eq_sum_range` and `HerbrandBridge.natFloor_ratCast`. All its
  other steps are restated here over `T : LocalField.TopologicalData K₀ L`, using the
  general definitions of `Herbrand.GeneralFinite`. The one p-adic ingredient, the
  relative-integer lemma `PadicField.TopologicalData.relative_mem_integers_iff`, is
  replaced by step 1 below.

All declarations in `QuotientBridge` are internal lemmas. They connect the Library side
(real-indexed groups built from `integerAction`) to the source side (rational-indexed
groups of `Langlands.Ramification.lowerGroup`).

## Proof (as implemented)

1. **Relative integers without a p-adic norm** (section `Relative`). Let
   `S : LocalField.TopologicalData K₀ E`, `T : LocalField.TopologicalData K₀ L` and
   `f : E →ₐ[K₀] L`. Then `algHom_mem_integers_iff S T f x` states
   `f x ∈ T.Integers ↔ x ∈ S.Integers`. Both realizations' topologies, valuative
   relations, module topologies and local-field certificates are installed. `f` is
   injective, so `LinearMap.exists_leftInverse_of_injective` gives a `K₀`-linear `g` with
   `g ∘ f = id`. Both `f` and `g` are continuous for the `K₀`-module topologies
   (`IsModuleTopology.continuous_of_linearMap`). A private copy of
   `valuation_lt_one_iff_pow_tendsto` from `Herbrand/GeneralTransport.lean` says that, in a
   nonarchimedean local field, `v(y) < 1` exactly when `y ^ n → 0`. Applying `f` or `g` to
   the sequence of powers (with `map_pow`, `map_zero` and `g (f y) = y`) gives
   `v(f y) < 1 ↔ v(y) < 1` for all `y`. For `x ≠ 0`, testing `y = x⁻¹` with `inv_lt_one₀`
   gives `v(f x) ≤ 1 ↔ v(x) ≤ 1`. The case `x = 0` is immediate. No hypothesis on `K₀`
   is used. `fixedField_mem_integers_iff` is the case where `f` is the inclusion
   `IsScalarTower.toAlgHom K₀ E_H L` of the actual fixed field.
2. **Library φ at rational points** (section `Phi`). Suppose the Library orders
   `lowerGroupOrder T K i` equal the source cardinalities
   `Langlands.Ramification.lowerGroupCard A Γ i` for all `i`. Then for every rational `u ≥ 0`,
   the Library real `herbrandPhi T K` at `u` is the cast of the source rational
   `herbrandPhi` at `u` (`herbrandPhi_ratCast`). Both are given by the floor formula
   (`herbrandPhi_floor` of `GeneralFinite`, `Langlands.Ramification.herbrandPhiRat_of_pos`).
   `herbrandPhi_natCast_eq` is the case of natural numbers. For finite `Γ`, the ceiling of
   the Library `ψ` at a rational `w ≥ 0` is the source index
   `upperRamificationIndex A Γ w` (`ceil_herbrandPsi_ratCast`). This uses that `φ` and `ψ`
   are inverse strictly increasing bijections. Hence the Library upper group at `w` is the
   Library lower group with that index (`upperRamificationGroup_ratCast`, via
   `upperRamificationGroup_eq_lower`). The Library `φ` takes the rational value
   `(∑_{i<n} |G_{i+1}|) / |G_0|` at a natural number `n` (`herbrandPhi_natCast_rat`). The
   Library upper group is constant for `w` between `v` and `φ(⌈ψ(v)⌉)`
   (`upperRamificationGroup_eq_of_le`). So for every `v > -1` there is a rational `q ≥ 0`
   with `v ≤ q` such that `G^w = G^v` whenever `v ≤ w ≤ q`
   (`exists_rat_upperRamificationGroup_eq`). Finally, `lowerRamificationGroupReal_of_ceil_eq`
   says that `G_u` is the natural-index group `G_n` when `⌈u⌉ = n`.
3. **Source hypotheses** (sections `Source`, `Galois`). The Library lower groups and
   orders of `T` over `K` are, by definition, the source lower groups and cardinalities of
   `T.Integers` under `integerAction T K` (`lowerRamificationGroup_eq_source`,
   `lowerGroupOrder_eq_source`, both `rfl`). The action is faithful
   (`integerAction_faithful`): two automorphisms that agree on `T.Integers` agree on its
   fraction field `L` (`IsFractionRing.ringHom_ext`). `T.Integers` is a discrete valuation
   ring with finite residue field. `FiniteDimensional K L` follows from
   `Module.Finite.of_restrictScalars_finite K₀ K L`. The residue field of the fixed subring
   of `G` embeds into that of `T.Integers` and so is finite, hence perfect. This gives the
   separability that the ported theorem needs. With these,
   `source_map_lowerRamificationGroup_mk` is the ported Herbrand theorem for
   `T.Integers`, `G` and a normal `H`.
4. **Fixed fields.** By step 1, an element of `E_H` lies in `S.Integers` exactly when it
   lies in `T.Integers`. This gives `fixedSubringEquiv`. It intertwines the action of the
   coset of `g` in `G ⧸ H` on the fixed subring with the action of
   `AlgEquiv.restrictNormalHom E_H g` on `S.Integers` (`fixedSubringEquiv_smul`, from
   `AlgEquiv.restrictNormalHom_apply`). Through `IsGalois.normalAutEquivQuotient`, the
   transport lemmas then turn source statements about `G ⧸ H` into Library statements about
   `Gal(E_H/K)`. This gives `map_restrictNormalHom_eq` (images of lower groups) and
   `lowerGroupOrder_fixedField_quotient` (orders). The Library orders of `L/E_H` are the
   source orders of `H` (`lowerGroupOrder_fixedField`, through
   `IntermediateField.subgroupEquivAlgEquiv` and the identity of `T.Integers`).
5. **Upper numbering** (`upperQuotientCompatibility`). At `v = -1` both upper groups are the
   whole group (`upperRamificationGroup_neg_one`), and `restrictNormalHom` is surjective.
   For `v > -1`, step 2 gives rationals `q_T` for `L/K` and `q_S` for `E_H/K`. Let
   `w = min q_T q_S`. Then `w ≥ 0`, and replacing `v` by `w` changes neither upper group. At
   `w` both upper groups are Library lower groups with the source indices (step 2, with the
   orders of steps 3 and 4). The ported upper-numbering theorem, with step 3's lower-numbering
   input, and `map_restrictNormalHom_eq` then identify them.
6. **φ tower** (`herbrandPhi_fixedField_tower`). For rational `u ≤ 0` all three functions are
   the identity (`herbrandPhi_of_nonpos`). For rational `u > 0`, step 2 rewrites the three
   Library functions as source functions, with the orders of steps 3 and 4. The inner value
   is nonnegative by `herbrandPhi_pos`. The ported φ-transitivity theorem then applies. Both
   sides are continuous in `u` (`herbrandPhi_continuous`) and agree on the dense set of
   rationals, so they agree everywhere (`Continuous.ext_on`, `Rat.denseRange_cast`).
7. **Lower numbering** (`herbrandNormalSubgroup`). `G_u = G^{φ_{L/K}(u)}`
   (`upperRamificationGroup_phi`), and `φ_{L/K}(u) ≥ -1` by monotonicity. Step 5 maps this
   onto the upper group of `E_H/K` at `φ_{L/K}(u)`. By step 6 this index equals
   `φ_{E_H/K}(φ_{L/E_H}(u))`. `upperRamificationGroup_phi` for `S` turns the upper group
   back into the lower group at `φ_{L/E_H}(u)`.
8. **Subgroups** (`lowerSubgroupCompatibility`). The range of
   `AlgEquiv.restrictScalarsHom K` on `Gal(L/E_H)` is `H`
   (`range_restrictScalarsHom_fixedField`, from `IntermediateField.fixingSubgroup_fixedField`
   and `IntermediateField.fixingSubgroupEquiv`). This lemma needs `FiniteDimensional K L`. It
   takes it as a binder because `K₀` does not occur in its statement; the main theorem
   supplies it from `[FiniteDimensional K₀ L]`. At `u = -1` both real lower groups are the
   whole group (`lowerRamificationGroupReal_neg_one`), so both sides are `H`. For `u > -1`
   with `⌈u⌉ = n`, both real groups are the natural-index groups at `n`
   (`lowerRamificationGroupReal_of_ceil_eq`). An automorphism over `E_H` and its scalar
   restriction act identically on `T.Integers`
   (`restrictScalars_mem_lowerRamificationGroup_iff`, by `Iff.rfl`). So the two memberships
   correspond.

## Checks

The module was compiled in the pinned environment, with no errors or warnings. A private check file
compared the types of `upperQuotientCompatibility`, `herbrandNormalSubgroup` and
`lowerSubgroupCompatibility` with the binder list above by syntactic equality of the
elaborated types. All three agree. The three theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
