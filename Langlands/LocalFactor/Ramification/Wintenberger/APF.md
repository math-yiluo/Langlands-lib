# Arithmetically profinite extensions in the Library's filtrations

Module `Langlands.LocalFactor.Ramification.Wintenberger.APF`, namespace
`Langlands.Ramification.Wintenberger`.

Wintenberger's notions of §1 are defined in the FontaineWintenberger library from the absolute
upper filtration of a base field `K` in `SeparableClosure K` and from fixing subgroups:
`apfSubgroup K L u = G_L ⊔ G_K^u`, `IsAPF K L` (the subgroups `G_L ⊔ G_K^u`, `u ≥ −1`, are open,
for every embedding of `L`), `IsElementary K L i` (Wintenberger 1.3.1: `G_L ⊔ G_K^i` is everything
and `G_K^u ≤ G_L` for `u > i`), `IsElementaryStep` (the same for a step of finite subfields, over
its base with the spectral norm), `apfIndex K L u` (the index `(G_K^0 : (G_L ⊓ G_K^0) G_K^u)`) and
`apfPsi K L u = ∫₀ᵘ apfIndex K L (max v 0) dv` (Wintenberger 1.2.1). With the equality of the
absolute filtrations (`Absolute.upperRamificationGroupInfinite_eq_absolute`), each of them is a
statement about the Library's filtration `Local.absoluteUpperRamificationGroup K₀ K Ω hbase`, in any
separable closure `Ω`. This file states these translations.

## Main statements

Generic group theory, for an isomorphism `e : Ω₁ ≃ₐ[B] Ω₂` of extensions of a field `B`:

- `fixingSubgroup_map_autCongr (e) (S : IntermediateField B Ω₁) :
  S.fixingSubgroup.map e.autCongr.toMonoidHom = (S.map e.toAlgHom).fixingSubgroup`.
- `continuous_autCongr (e) : Continuous e.autCongr` for the Krull topologies, and the homeomorphism
  `autCongrHomeomorph e`.

For `K₀` with `hbase` as in `Absolute`, and `K` a normed extension of `K₀`
(`[NormedAlgebra K₀ K] [FontaineWintenberger.IsCompleteDiscreteValuedField K]
[FiniteDimensional K₀ K]`):

- `absoluteUpperRamificationGroup_map_autCongr (e : Ω₁ ≃ₐ[K] Ω₂) {v : ℝ} (hv : -1 ≤ v) :
  (Local.absoluteUpperRamificationGroup K₀ K Ω₁ hbase v).map e.autCongr.toMonoidHom =
  Local.absoluteUpperRamificationGroup K₀ K Ω₂ hbase v`: the Library's filtration does not depend
  on the separable closure.
- `apfSubgroup_eq_map (e : Ω₁ ≃ₐ[K] SeparableClosure K) (S : IntermediateField K Ω₁) {v : ℝ}
  (hv : -1 ≤ v) : FontaineWintenberger.apfSubgroup K (S.map e.toAlgHom) v =
  (S.fixingSubgroup ⊔ Local.absoluteUpperRamificationGroup K₀ K Ω₁ hbase v).map
  e.autCongr.toMonoidHom`.
- `isElementary_of_absoluteUpper (f : L →ₐ[B] Ω) {i : ℝ} (hi : 0 < i)
  (htop : f.fieldRange.fixingSubgroup ⊔ Local.absoluteUpperRamificationGroup K₀ B Ω hbase i = ⊤)
  (hfix : ∀ x : ℝ, i < x → Local.absoluteUpperRamificationGroup K₀ B Ω hbase x ≤
  f.fieldRange.fixingSubgroup) : FontaineWintenberger.IsElementary B L i`, for a finite separable
  extension `L` of a normed extension `B` of `K₀` and a separable closure `Ω` of `B`.
- `spectralNormedAlgebraOfTower K₀ K B`: for an algebraic extension `B` of a normed extension `K`
  of `K₀`, with the spectral norm over `K`, the normed `K₀`-algebra structure on `B` with its given
  algebra structure.
- `isElementaryStep_of_absoluteUpper (E E' : FontaineWintenberger.FiniteIntermediateField K
  (SeparableClosure K)) (hEE' : E ≤ E') [FiniteDimensional K₀ E.val] (Ω : Type uΩ) …
  [IsSepClosure E.val Ω] (f : IntermediateField.extendScalars hEE' →ₐ[E.val] Ω) {i : ℝ}
  (hi : 0 < i) (htop : …) (hfix : …) : FontaineWintenberger.IsElementaryStep K E E' hEE' i`: the
  two conditions of Wintenberger 1.3.1 for the Library's filtration of the base `E` (over `K₀`)
  give an elementary step in the sense of the FontaineWintenberger library.
- `isAPF_iff_isOpen (i : L →ₐ[K] Ω) : FontaineWintenberger.IsAPF K L ↔ ∀ u : ℝ, -1 ≤ u →
  IsOpen ((i.fieldRange.fixingSubgroup ⊔ Local.absoluteUpperRamificationGroup K₀ K Ω hbase u :
  Subgroup (Ω ≃ₐ[K] Ω)) : Set (Ω ≃ₐ[K] Ω))`, for `L/K` separable and `Ω` a separable closure.
- `apfIndex_eq_relIndex (i : L →ₐ[K] Ω) {u : ℝ} (hu : 0 ≤ u) : FontaineWintenberger.apfIndex K L u
  = ((i.fieldRange.fixingSubgroup ⊓ G^0) ⊔ G^u).relIndex G^0`, with
  `G^v = Local.absoluteUpperRamificationGroup K₀ K Ω hbase v`.
- `apfPsi_eq_self_of_sup_eq_top (i : L →ₐ[K] Ω) {μ : ℝ} (htop : i.fieldRange.fixingSubgroup ⊔
  G^μ = ⊤) {u : ℝ} (hu : u ≤ μ) : FontaineWintenberger.apfPsi K L u = u`.

## Proofs

An isomorphism of separable closures conjugates the FontaineWintenberger filtrations
(`FontaineWintenberger.upperRamificationGroupInfinite_map_autCongr`), hence the Library's, which
are equal to them. Fixing subgroups are conjugated by `fixingSubgroup_map_autCongr`. Continuity of
conjugation is checked on the basic open subgroups, the fixing subgroups of finite subextensions.
The translations of `IsElementary` and `IsAPF` then use the copy's criteria with one embedding
(`IsElementary.of_embedding`, `isAPF_iff_embedding`); the index is a relative index of images
under the injective map `e.autCongr`. If `G_L ⊔ G^μ = ⊤`, then for `0 ≤ v ≤ μ` the group
`(G_L ⊓ G^0) ⊔ G^v` contains `G^0` (write `σ = τδ` with `τ ∈ G_L`, `δ ∈ G^v`, so `τ ∈ G^0`), so
`apfIndex K L v = 1` and the integral defining `apfPsi` is `u`.

## Declarations used

From the FontaineWintenberger library: `apfSubgroup`, `IsAPF`, `isAPF_iff_embedding`,
`isAPFSubextension_iff`, `IsElementary`, `IsElementary.of_embedding`, `IsElementaryStep`,
`normedAlgebra_isCompleteDiscreteValuedField`, `apfIndex`, `apfIndex_eq_embedding`,
`apfInertiaIndex`, `apfInertiaSubgroup`, `apfPsi`, `apfPsi_of_nonpos`, `absoluteUpperRamificationGroup`,
`upperRamificationGroupInfinite_map_autCongr`, `FiniteIntermediateField`. From the Library:
`Local.absoluteUpperRamificationGroup`, `Local.absoluteUpperRamificationGroup_antitone`.
From Mathlib: `krullTopology_mem_nhds_one_iff`, `IsSepClosure.equiv`, `spectralNorm.normedAlgebra`.

## Sources

Wintenberger 1983, §1.2 (arithmetically profinite extensions, Definition 1.2.1 and the function
`ψ_{L/K}`) and §1.3.1 (elementary extensions).
