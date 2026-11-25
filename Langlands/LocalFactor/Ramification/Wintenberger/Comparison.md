# Wintenberger's comparison in the Library's filtrations

Module `Langlands.LocalFactor.Ramification.Wintenberger.Comparison`, namespace
`Langlands.Ramification.Wintenberger`.

This file states Wintenberger's Corollaires 3.2.3 and 3.3.6 for an infinite, arithmetically
profinite, totally ramified extension of a `p`-adic field in the Library's own notions: the
absolute Galois group of the extension is that of the Laurent series field `k((t))` over the
residue field of the base, with the upper filtrations matched by Wintenberger's function `ψ` and
the residue degrees preserved.

## Main statements

- `laurentSeriesCongr (f : k ≃+* k') : LaurentSeries k ≃+* LaurentSeries k'` (coefficientwise), with
  `valued_laurentSeriesCongr : Valued.v (laurentSeriesCongr f x) = Valued.v x`.
- `continuous_restrictScalarsHom R S A [Algebra.IsAlgebraic R A] :
  Continuous (AlgEquiv.restrictScalarsHom R : (A ≃ₐ[S] A) →* (A ≃ₐ[R] A))` for the Krull
  topologies.
- `padicFieldResidueEquiv F`: the residue field of the unit ball of the canonical norm of a
  `p`-adic field `F` is `Weil.Local.localResidueField F`.
- `apfResidueEquiv (L) (hAPF : FontaineWintenberger.IsAPF F.Carrier L)
  (htot : L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 = ⊤) :
  IsLocalRing.ResidueField (integralClosure 𝒪_F L) ≃+* Weil.Local.localResidueField F`, for an
  intermediate field `L` of `AlgebraicClosure F.Carrier`, `𝒪_F` the unit ball of the canonical norm.
- `padic_norm_le_one_iff F a` and `padic_mem_extensionIntegers_iff F x`: the unit balls of the
  canonical norm of `F` and of the Library's normed-field adapter `LocalGalois.localNormedField`
  (for `F.canonicalTopologicalData`) coincide, and so do the integers of `AlgebraicClosure F.Carrier`
  for the two norms.
- `padic_algebraicResidueAut_isFrobPow F σ (h : IsFrobPow (LocalGalois.residueHom F.Carrier
  (AlgebraicClosure F.Carrier) σ) q M) : IsFrobPow (FontaineWintenberger.algebraicResidueAut
  F.Carrier (AlgebraicClosure F.Carrier) σ) q M`: the Library's residue action of `σ` (adapter norm)
  and the FontaineWintenberger residue action (canonical norm) are the same Frobenius power.
- `padic_isFrobPow_of_localResidueDegree F σ n (hn : Weil.Local.localResidueDegree F σ =
  Weil.frobenius n) : IsFrobPow (FontaineWintenberger.algebraicResidueAut F.Carrier
  (AlgebraicClosure F.Carrier) σ) (Nat.card (Weil.Local.localResidueField F))
  (-Multiplicative.toAdd n)`.
- `padic_exists_localResidueDegree_eq F L (htot) (n : Weil.Degree) : ∃ a : AlgebraicClosure
  F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier, Weil.Local.localResidueDegree F
  (AlgEquiv.restrictScalarsHom F.Carrier a) = Weil.frobenius n`, for `L` with
  `G_L ⊔ G_F^0 = G_F`.
- `wintenbergerPsi (F) (L) (u : ℝ) : ℝ := ∫ v in 0..u,
  (((L.fixingSubgroup ⊓ G_F^0) ⊔ G_F^{max v 0}).relIndex G_F^0 : ℝ)`, with
  `G_F^v = Padic.absoluteUpperRamificationGroup F v`: Wintenberger's `ψ_{L/F}` in the Library's
  filtration, and `wintenbergerPsi_eq_apfPsi` identifying it with the FontaineWintenberger
  `apfPsi` (for the canonical norm of `F`).
- `normFieldComparison (F : PadicField.{u} p) (L : IntermediateField F.Carrier
  (AlgebraicClosure F.Carrier)) (hinf : ¬ Module.Finite F.Carrier L)
  (hopen : ∀ v : ℝ, -1 ≤ v → IsOpen ((L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F v
  : Subgroup (Field.absoluteGaloisGroup F.Carrier)) : Set (Field.absoluteGaloisGroup F.Carrier)))
  (htot : L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 = ⊤) :
  ∃ θ : (AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier) ≃ₜ* (Ω ≃ₐ[X] Ω),
  (∀ u : ℝ, -1 ≤ u → ((Padic.absoluteUpperRamificationGroup F u).comap
  (AlgEquiv.restrictScalarsHom F.Carrier)).map θ.toMulEquiv.toMonoidHom =
  Local.localAbsoluteUpperRamificationGroup X Ω (wintenbergerPsi F L u)) ∧
  ∀ a, Weil.Local.localResidueDegree F (AlgEquiv.restrictScalarsHom F.Carrier a) =
  Weil.Local.SepClosed.localResidueDegree X Ω (θ a)`, where
  `X = LaurentSeries (Weil.Local.localResidueField F)` with `LocalField.Laurent.valuativeRel` and
  `Ω = SeparableClosure X`.

## Proofs

The residue field: `G_L ⊔ G_F^0 = G_F` makes the APF residue layer of `L`
(`FontaineWintenberger.apfResidueLayer`) of residue degree one
(`apfSubgroup_index_zero_eq_residueDegree`, through `APF.apfSubgroup_eq_map`), and the residue field
of `L` is that of this layer (`integralClosureResidueEquiv`).

`normFieldComparison`: `hopen` is arithmetic profiniteness (`APF.isAPF_iff_isOpen`), so the field of
norms `X_F(L)` exists, and `FieldOfNorms.laurentEquiv` (Wintenberger, Théorème 2.1.3 with the
residue field of `L`) composed with `laurentSeriesCongr (apfResidueEquiv …).symm` identifies `X`
with `X_F(L)`, compatibly with the valuations (`FieldOfNorms.laurentEquiv_valuation`). The
isomorphism `θ` is the composite of the copy's `RelFieldOfNorms.krullEquiv` (Corollaire 3.2.3),
restriction of scalars from `X_F(L)` to `X` (`NormField.restrictScalarsMulEquiv`) and conjugation by
an isomorphism of separable closures of `X`; it is continuous, from a compact group to a Hausdorff
one, hence a homeomorphism. For the filtrations: Corollaire 3.3.6 of the copy
(`RelFieldOfNorms.upperRamificationGroup_eq_comap`) and `Absolute.upperRamificationGroupInfinite_eq_padic`
turn `G_F^u ∩ G_L` into the copy's filtration of the field of norms at `ψ(u)`;
`NormField.mem_normUpperRamificationGroup_iff` identifies that with the Library's filtration of `X`
in the relative field of norms, and `APF.absoluteUpperRamificationGroup_map_autCongr` moves it to
`SeparableClosure X`.

For the residue degrees, both sides are continuous homomorphisms of the compact group `Gal(F̄/L)`
to the profinite integers, so by `Degree.eq_of_frobenius` it suffices that every integral degree
occurs on the `F` side (`padic_exists_localResidueDegree_eq`: the Library's
`Weil.Local.localResidueDegree_surjective`, the decomposition `G_F = G_L G_F^0` and
`G_F^0 = ker`, from `HerbrandBridge.absoluteUpperCanonicalInertia` and
`Weil.Local.localResidueDegree_ker`) and that an integral degree on the `F` side is the same
degree on the `X` side. For the latter, an integral degree is a Frobenius-power residue action
(`localResidueDegree_eq_frobenius_iff`), which passes from the adapter norm to the canonical norm
(`padic_algebraicResidueAut_isFrobPow`, the two norms having the same integers), then to the relative
field of norms and to `SeparableClosure X` (`NormFieldResidue.relFieldOfNorms_localResidueDegree`),
with `#k_X = #k` (`LocalField.Laurent.residueCardinality_eq`).

In the setting of the proof, the integers of `F` act on `L` through `F` (`integersAlgebra`), as in
the FontaineWintenberger library, so that its residue field of `L` is the one appearing in
`FieldOfNorms.laurentEquiv`. Two declarations carry `set_option maxHeartbeats 400000`.

## Declarations used

From the FontaineWintenberger library: `IsAPF`, `IsAPF.apfPsi_mem_Ici`, `apfPsi`, `apfIndex`,
`apfResidueLayer`, `integralClosureResidueEquiv`, `integralClosure_valuationRing`,
`apfSubgroup_index_zero_eq_residueDegree`, `closure_isSepClosure`, `FieldOfNorms`,
`FieldOfNorms.uniformizer`, `FieldOfNorms.valuation_uniformizer`, `FieldOfNorms.laurentEquiv`,
`FieldOfNorms.laurentEquiv_valuation`, `RelFieldOfNorms`, `RelFieldOfNorms.krullEquiv`,
`RelFieldOfNorms.normUpperRamificationGroup`, `RelFieldOfNorms.upperRamificationGroup_eq_comap`.
From `Wintenberger`: `relFieldOfNorms_localResidueDegree`, `localResidueDegree_eq_frobenius_iff`,
`eq_of_frobenius`, `FrobPowAt.of_map`, `mem_canonicalIntegers_iff`, `padicBaseNorm_compatible`.
From the Library: `Weil.Local.localResidueDegree`, `Weil.Local.localResidueDegree_surjective`,
`Weil.Local.localResidueDegree_ker`, `HerbrandBridge.absoluteUpperCanonicalInertia`,
`Padic.absoluteUpperRamificationGroup_normal`, `LocalField.Laurent.residueCardinality_eq`,
`LocalGalois.localNormedField_le`, `LocalGalois.extensionIntegers`, `LocalGalois.residueHom`,
`Padic.absoluteUpperRamificationGroup`, `Local.localAbsoluteUpperRamificationGroup`,
`LocalField.Laurent.valuativeRel`, `LocalField.Laurent.localField`, `Weil.Local.localResidueField`,
`LocalGalois.localNormedField`. From Mathlib: `HahnSeries.map`, `HahnSeries.map_mul`,
`LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero`, `krullTopology_mem_nhds_one_iff`,
`IntermediateField.finiteDimensional_adjoin`, `spectralValue_le_one_iff`,
`IntermediateField.fixingSubgroupEquiv`, `Subgroup.mem_sup_of_normal_right`.

## Sources

Wintenberger 1983, Théorème 2.1.3 (the field of norms is a local field of characteristic `p`,
isomorphic to `k_L((t))`), Corollaire 3.2.3 (`G_L ≃ G_{X_K(L)}`), Corollaire 3.3.6 (the upper
filtrations correspond through `ψ_{L/K}`), and §1.2.1 (the function `ψ_{L/K}`).
