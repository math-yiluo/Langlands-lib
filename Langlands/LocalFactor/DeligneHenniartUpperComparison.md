# Upper groups of intermediate Weil groups and the half-break comparison

Lean module: `Langlands.LocalFactor.DeligneHenniartUpperComparison`. It imports
`Langlands.LocalFactor.DeligneHenniartInductionStep` (my candidate c11172a2),
`Langlands.LocalFactor.Ramification.Herbrand.SlopeProof` (my accepted candidate f6a60324) and
the Library module `Langlands.LocalFactor.CommonClosureIntermediateWeil`.

Notation: `F : PadicField.{u} p`, and `E, L` are finite intermediate fields (`Extension F`).
`ψ_{E/F}` is `relativeHerbrandPsi E` (module `SubextensionProof`), `G_F^v` is
`absoluteUpperRamificationGroup F v`, `G_E` is `E.field.fixingSubgroup`, and `I_F` is
`F.absoluteInertia F.canonicalTopologicalData`. `e_F` and `e_E` are the canonical ramification
indices `F.canonicalTopologicalData.ramificationIndex` and `(fieldData F E).ramificationIndex`.

## Part 1: integer forms of the slope (namespace `Langlands.Ramification.HerbrandBridge`)

### Finite level

These results are for a finite Galois `L` with realization `T`, a base `K` and an
intermediate `E`. `H` is the image of `Gal(L/E)` in `Gal(L/K)`, and `G_i` are the lower groups
of `L/K`.

- `lowerGroupOrder_subfield_le`: `|G_i ∩ H| ≤ |G_i|`. It follows from
  `lowerGroupOrder_subfield_mul_relIndex` (module `ConvexityProof`), since the relative index
  is positive.
- `herbrandPhi_le_mul`: `φ_{L/E}(y) ≤ [G_0 : G_0 ∩ H] · φ_{L/K}(y)` for `y ≥ 0`. Both sides
  are ramp sums divided by the orders at `0` (`herbrandPhi_eq_sum`), and the weights compare
  termwise.
- `herbrandPhi_herbrandPsi_le_mul`: `φ_{L/E}(ψ_{L/K}(s)) ≤ [G_0 : G_0 ∩ H] · s` for `s ≥ 0`.

### Absolute level

- `relativeSubgroup_relIndex_eq`: the index of the image of `Gal(M/K)` in the inertia group of
  `M/F` equals the absolute index of `I_F ∩ G_K` in `I_F`. Here `G_K` is the preimage of
  `relativeSubgroup` under `absoluteRelativeRestriction` (module `SlopeProof`). The proof is
  the image of `G_F^0 = I_F`, then `Subgroup.relIndex_comap`.
- `relativeIndex_le_relIndex_mul` and `relativeHerbrandPsi_le_relIndex_mul`:
  `ψ_{E/F}(s) ≤ [I_F : I_F ∩ G_E] · s` for `s ≥ 0`.
- `fieldData_ramificationIndex_eq`: `e_E = [I_F : I_F ∩ G_E] · e_F` as reals. This is
  `fixingSubgroup_relIndex_absoluteInertia_mul` from `SlopeProof`.

### Multiplied forms

- `ramificationIndex_mul_relativeHerbrandPsi_le E hs`: `e_F · ψ_{E/F}(s) ≤ e_E · s` for
  `s ≥ 0`. So the slopes of `ψ_{E/F}` are at most `e(E/F)`.
- `ramificationIndex_mul_relativeHerbrandPsi_sub E hv₀ hG hs hst`: if `0 ≤ v₀` and
  `G_F^{v₀} ≤ G_E`, then `e_F · (ψ_{E/F}(t) - ψ_{E/F}(s)) = e_E · (t - s)` for
  `v₀ ≤ s ≤ t`.
- `ramificationIndex_mul_relativeHerbrandPsi_sub_of_upperGroup_le`: the same, with the
  hypothesis `upperGroup F v₀ ≤ weilSubgroup F E` on the actual Weil groups. This uses
  `relativeHerbrandPsi_sub_eq_of_upperGroup_le` from `SlopeProof`.

## Part 2: upper groups inside `W_L` (namespace `Langlands.LocalFactor.NonabelianSystem.DeligneHenniart`)

- `weilUpperSubgroup F L s` is the named definition. It is the upper group of index `s` of the
  Weil group of `L.asPadicField`, as a subgroup of `weilSubgroup F L`. It is the preimage of
  `upperGroup (L.asPadicField) s` under the inverse of the Library identification
  `standaloneWeilEquiv F L`. `mem_weilUpperSubgroup` unfolds the membership.
- `weilUpperSubgroup_antitone` and `weilUpperSubgroup_normal`.
- `weilUpperSubgroup_le_inertia`: for `s ≥ 0`, `weilUpperSubgroup F L s` lies in
  `CommonClosureWeilDeligne.inertia F L`. The proof uses `absoluteUpperCanonicalInertia`,
  `localInertia_eq_comap` and `standaloneWeilEquiv_symm_mem_inertia`. These are the
  normality and inertia hypotheses of `exactWitnessOn_characterClass` in
  `DeligneHenniartRelativeWitness`.
- `coe_mem_upperGroup_iff F L hv x`: for `v ≥ -1` and `x ∈ W_L`, `x ∈ upperGroup F v` if and
  only if `x ∈ weilUpperSubgroup F L (ψ_{L/F}(v))`. This is Herbrand's theorem
  `intermediateWeilEquiv_mem_upperGroup_iff` (module `SubextensionProof`), read through
  `standaloneWeilEquiv`.
- `weilUpperSubgroup_eq_restrictSubgroup F L hL ha`: for `a ≥ -1`,
  `weilUpperSubgroup F L (ψ_{L/F}(a)) = restrictSubgroup F (baseExtension F) L hL (baseUpperGroup F a)`,
  i.e. `W_L^{ψ(a)} = W_F^a ∩ W_L`.
- `weilUpperSubgroup_half_le_restrictSubgroup F L hL ha`: for `a ≥ 0`,
  `W_L^{ψ_{L/F}(a)/2} ⊆ W_F^{a/2} ∩ W_L`. It follows from `ψ(a/2) ≤ ψ(a)/2`
  (`relativeHerbrandPsi_half_le`, module `ConvexityProof`) and antitonicity.
- `exactWitnessOn_induce_upper hsys L hL ha ψ x γ hx`. Suppose `γ` is an exact witness for
  `x : Virtual F L` relative to `weilUpperSubgroup F L (ψ_{L/F}(a)/2)` and the trace
  character. Then `(baseExtension F).unitsNorm L hL γ` is an exact witness over the base field
  for `induce x`, relative to `baseUpperGroup F (a/2)`. This is `exactWitnessOn_induce` after
  `exactWitnessOn_mono`.
- `approximateWitnessOn_induce_upper`: the same with `ψ_{L/F}(a)` and `baseUpperGroup F a`,
  for `a ≥ -1`.

## Sources

- Deligne–Henniart (1981), §3.2, Proposition (iii) (printed p. 102, PDF p. 14). Past
  `α(M/L)`, the slope of `ψ_{M/L}` is the ramification index. Below it, the slopes are
  `e/p^k`, in particular at most `e`. The Lean statements are the bound by `e` on `[0, ∞)`
  and the equality past any `v₀ ≥ 0` with `G_F^{v₀} ⊆ G_E`. The finer statement `e/p^k` is
  not claimed.
- Deligne–Henniart (1981), §4.5 (printed p. 110, PDF p. 22) and §4.8 (printed p. 111,
  PDF p. 23). §4.8 states `β(W_i) ≤ ψ_{L_i/K}(β(W)) < ψ_{L_i/K}(α(V)/2) ≤ ψ_{L_i/K}(α(V))/2 = α(χ_i)/2`.
  On the level of tests, this is the inclusion `W_{L_i}^{ψ(α)/2} ⊆ W_K^{α/2} ∩ W_{L_i}` used
  in `exactWitnessOn_induce_upper`. The approximate case of §4.5 uses
  `W_{L_i}^{ψ(α)} = W_K^α ∩ W_{L_i}`.
- Serre, *Local Fields* IV §3, Proposition 15 and Remark 2 (printed pp. 74–75, PDF
  pp. 81–82): Herbrand's theorem for subgroups and the relative functions.
