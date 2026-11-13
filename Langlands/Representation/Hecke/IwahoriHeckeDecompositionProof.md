# Proof of Renard V.5.3: the decomposition of `H(G, K)`

Module `Langlands.Representation.Hecke.IwahoriHeckeDecompositionProof`, namespace
`Langlands.Hecke`. Worker 127 wrote it for Task 5575. The theorem
`iwahoriHeckeDecomposition : IwahoriHeckeDecompositionStatement.{u}` proves the
published proposition `Langlands.Hecke.IwahoriHeckeDecompositionStatement`
exactly, with universe `u` and no additional hypothesis.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, V.5.3
(printed pp.123–125 / PDF pp.129–131). The proof follows Renard's computations
for items 1–4, 6 and 7. For item 5 it does not use V.3.24, which fails in
general, as the statement's Markdown explains. It does not use Gordan's lemma
either. Instead it applies Dickson's lemma to floor coordinates, through
`IwahoriHeckeCore`. The proof uses `set_option maxHeartbeats 1000000`, a finite
limit, because the single declaration elaborates the whole reductive setting.

## Notation in the proof

`B = (𝔅.datum F G hG).base`, `i = B.i : S → G`, `j = map B.centralizer.j`,
`s = B.centralizer.s`. `Φ⁺ = positiveRelativeRoots i ν` is finite by
`IsSplitTorus.finite_positiveRelativeRoots`. The proof uses the following
abbreviations:

- `c y = uniformizerPowers i (ofAdd y) = i(y(ϖ))` for `y ∈ X_*(S)`;
- `σ y = s(y(ϖ)) ∈ Z(F)`. `hjs` shows `j (σ y) = c y`, from
  `s ≫ j = i` (`B.centralizer.comp_eq`).

## Steps

1. **Basic facts.** `K₀` is compact by
   `availableCompactCore (𝔅.datum F G hG) h𝔅.groupAxioms ν hν x hx`.
2. **The minimal parabolic.** The hypothesis on `K` for `J = ∅` gives a compatible
   split component `q : A → S` and `StandardParabolicBasisMember i ν ∅ q K`, that
   is:
   - the Iwahori factorization `hIw`, a bijection
     `(K ∩ N̄) × (K ∩ M) × (K ∩ N) → K`, which, applied to `k⁻¹`, gives
     `k = n m nb` (`hdec`);
   - the contraction clauses `hcon`.

   `ν` is a standard cocharacter for `J = ∅`, because simple roots are positive.
   So `uniformizerPowers_mem_standardComponentChambers` puts `c y` into
   `standardComponentCA i q` and `standardComponentCAplus i ν ∅ q` for every `y`
   with `0 ≤ ⟨α, y⟩` on `Φ⁺` (`hchamber`). `LeviIntersectionNormalization` then
   gives `hconjM`, and `WeakChamberContraction` gives `hconjN` and `hconjNb`.
   Together these build `L : IwahoriLatticeData K X_*(S) Φ⁺` with
   `pair α = ⟨α, ·⟩`.
3. **Characterizations in `Z(F)`.** `hval` computes
   `⟨α, ν_Z(σ y · f)⟩ = ⟨α, y⟩ + ⟨α, ν_Z(f)⟩` for the centralizer valuation
   `centralizerValuation`, using `centralizerValuation_uniformizerSection`. It
   gives two descriptions:
   - `hCt`: `t' ∈ C̃⁺` if and only if `t' = σ y · f` with `f ∈ F₀` and
     `0 ≤ ⟨α, y⟩ + e α f` for all `α ∈ Φ⁺`, where `e α f = ⟨α, ν_Z(f)⟩`;
   - `hCp`: `z ∈ C⁺` if and only if `z = σ y` with `y` dominant, by
     `C0Plus_eq_inter_dominant`.
4. **Commutation.** `hcomm` shows that `c y` commutes with `j f` for dominant
   `y`. `c y` is the image of a point of the split component `A` (`hchamber`).
   `j f` lies in `standardLeviPoints i ν ∅`, via `map_mem_centralizerPoints`,
   `torusCentralizer_carrier_base` and `torusCentralizer_le_standardLevi`.
   `map_commute_standardLeviPoints` then gives the commutation.
5. **Dominant decomposition.** `hdecomp` writes every `d ∈ Z(F)^+` as `t' u` with
   `t' ∈ C̃⁺` and `u ∈ Z(F)^1`:
   - The transversal gives `f ∈ F₀` in the lattice class of `d`, so
     `ν(d) ν(f)⁻¹ = ν(s(σ'))` for some `σ' ∈ S(F)`.
   - `isUniformizerLatticeSection` writes `σ' = (σ' ϖ^{-y}) ϖ^y` with
     `σ' ϖ^{-y}` in the norm kernel of `S`. That kernel maps into the norm
     kernel of `Z` (`map_mem_rationalCommonNormKernel`), which is the kernel of
     the character valuation (`rationalCharacterValuation_ker`).
   - So `t' = σ y · f` has the valuation of `d`, and is dominant by
     `dominantCentralizer_mem_iff_of_characterValuation_eq`. Then
     `u = t'⁻¹ d` lies in `Z(F)^1`.
6. **Cartan.** `hcartan` gives `G = K₀ j(C̃⁺) K₀`. The published Cartan
   decomposition `parahoricCartanConclusions_of_satisfiesGroupAxioms` gives
   `G = P_x j(Z(F)^+) P_x`. It is combined with three facts:
   - `P_x ⊆ K₀` (`parahoricAt_le_compactStabilizer`);
   - `j(Z(F)^1) ⊆ K₀` (`IsOmegaCompatible.map_mem_compactStabilizer`);
   - step 5.

## The seven items

1. `span (a '' K₀)` is finite-dimensional, by `finite_image_massIndicator` and
   compactness of `K₀`. Linear independence comes from
   `linearIndepOn_range_massIndicator`. For `a x₁ = a x₂ ↔ x₁⁻¹ x₂ ∈ K`, use
   `massIndicator_eq_iff`. If `x₁ = k₁ x₂ k₂`, then
   `x₁⁻¹ x₂ = k₂⁻¹ (x₂⁻¹ k₁⁻¹ x₂) ∈ K` by normality. Conversely,
   `x₁ = x₂ (x₂⁻¹ x₁)`.
2. `massIndicator_mul_of_normalizes` and `massIndicator_mul_of_normalizes'` apply
   with the normality of `K` in `K₀`.
3. By `hCp`, write `z_i = σ y_i` and apply `L.massIndicator_mul_dominant`.
4. The generators commute: by item 3, `a (j z₁) a (j z₂) = a (j (z₁ z₂))`, and
   `σ y₁ σ y₂ = σ y₂ σ y₁`. Elements of the generated subalgebra then commute by
   `Algebra.commute_of_mem_adjoin_of_forall_mem_commute`, applied twice.
5. `L.exists_finite_left` with `fe f = j f` and the offsets `e` gives a finite set
   of admissible pairs. Its image `{σ t · f}` lies in `C̃⁺` by `hCt` and is
   enumerated by `Set.Finite.fin_embedding`. Each `a (j t')`, for
   `t' = σ y · f ∈ C̃⁺`, equals some `a (j (σ z)) * a (j (t k))` with
   `σ z ∈ C⁺`.
6. `span_sandwich_eq_top` with `T = j(C̃⁺)` (step 6) and
   `S = {a (j z) * D k}`, followed by reassociation of the products.
7. `L.exists_finite_right`, which uses `hcomm`, gives the right-handed generators
   as in item 5. `span_sandwich_eq_top` with `S = {a (j (t k)) * a (j z)}` gives
   the spanning statement.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.IwahoriHeckeDecompositionStatement` | the target |
| `Langlands.Representation.Hecke.IwahoriHeckeCore` | sandwich spanning, lattice data, finiteness lemmas |
| `Langlands.BruhatTits.Cartan.AvailableCartanProof` | `parahoricCartanConclusions_of_satisfiesGroupAxioms` |
| `Langlands.BruhatTits.SpecialCompact.AvailableCompactCore` | compactness of `K₀` |
| `Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics` | `uniformizerPowers_mem_standardComponentChambers` |
| `Langlands.Representation.Jacquet.StandardCentralContraction` | `map_commute_standardLeviPoints` |
| `Langlands.Representation.Plancherel.RenardDominantValuation` | `C0Plus_eq_inter_dominant`, `centralizerValuation_uniformizerSection`, `dominantCentralizer_mem_iff_of_characterValuation_eq` |
| `Langlands.Geometry.Building.CocharacterUniformizerProof` | `isUniformizerLatticeSection` |
| `Langlands.GroupScheme.Rational.RootSupportFiniteness` | `IsSplitTorus.finite_positiveRelativeRoots` |
