# Renard VI.9.1, Remark 3, from uniform stabilization and two-sided contraction

Author: Worker 5457. Module
`Langlands.Representation.Exponents.GeneralizedJacquetContractingRangeReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.9.1, Remarque 3 after the Proposition and the paragraph of the
proof beginning "Le troisième point résulte assez facilement du deuxième" (printed p.198 /
PDF p.204). That paragraph uses Théorème V.5.2 (printed p.123 / PDF p.129). Registered
source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Statement

`GeneralizedJacquetContractingRangeReductionStatement.{u, v}` is the implication

    UniformCompressionStabilizationStatement.{u, v} →
      SplitComponentOppositeContractionStatement.{u} →
        GeneralizedJacquetContractingRangeStatement.{u, v}

between three propositions. None of them is changed here.

* `RationalPointFamily.UniformCompressionStabilizationStatement` (published) is the
  Proposition of VI.9.1, for the dynamic parabolic of a cocharacter `χ`. For `K` and an
  `M`-central Iwahori contraction `g`, it gives one exponent `b`, chosen before the
  representation, with the following property. From `b` on, the power kernels and power
  ranges of `A_g : v ↦ e_K(π(g) v)` on `V^K` are the kernel supremum `V^K_0` and the stable
  image `V^K_*`, and these two submodules split `V^K`.
* `SplitComponentOppositeContractionStatement` (Worker 167, candidate
  `955c9df6-04a7-4e8c-a8d7-f00232570027`, accepted) is the two-sided form of Renard V.5.2
  (iii) on all of `A^+(ε)`. Take compact `C ⊆ N(F)` and `C̄ ⊆ N̄(F)` and a neighbourhood
  `L` of `1`. Then there is `ε > 0` such that `t c t⁻¹ ∈ L` for `c ∈ C` and `t⁻¹ c t ∈ L`
  for `c ∈ C̄`, for every `t ∈ A(F)` with `|α(t)| < ε` for all `α ∈ Δ(P)`.
* `GeneralizedJacquetContractingRangeStatement` (published) is Remark 3 for an actual
  rational parabolic `P = MN` with opposite `P̄ = MN̄`. For an `M`-central Iwahori
  contraction `t₀` of `K`, there is `ε > 0` with the following property. For every
  `t ∈ A^+(ε)` and every smooth representation, `ker A_t = V^K_0(t₀)` and
  `Im A_t = V^K_*(t₀)`.

Provenance: the implication as a single proposition is ours. Renard deduces Remark 3 from
the Proposition, from Remark 2 and from Théorème V.5.2. This statement is recorded as an
intermediate result. Unconditional proofs of the two antecedents are still needed for the
task's target.

`generalizedJacquetContractingRange_of_uniformStabilization` proves the statement at
arbitrary universes `u, v`. It uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Proof

The proof keeps the binders of the target. Write `N(F) = pointImage (n ≫ p)`,
`M(F) = pointImage (m ≫ p)` and `N̄(F) = pointImage (nbar ≫ pbar)`.

1. **Dynamic description.** The Library theorems `parabolicDynamic` and
   `dynamicGeometricUnipotentRadical` feed
   `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`. This gives a cocharacter `χ`
   with `P` the dynamic parabolic and `M` the dynamic centralizer of `χ`. Then
   `pointImage_radical_eq_dynamic`, `pointImage_eq_range_carrier` and
   `pointImage_opposite_radical_eq_dynamic` (with `oppositeDynamicParabolicUniqueness`)
   identify `N(F)`, `M(F)` and `N̄(F)` with the dynamic radical, the centralizer and the
   opposite radical. Rewriting along these equalities transports the uniform stabilization
   Proposition to every `M(F)`-central element `g` with
   `IsIwahoriContraction K N(F) M(F) N̄(F) g` (the local `hstab'`). The same pattern
   appears in the Library module `LeviJacquetOppositePairingStructure`.
2. **Exponent.** Apply this to `t₀` to get `b₀`, and put `b = max b₀ 1`. Then
   `V^K_*(t₀) = Im A_{t₀}^b` and `V^K_0(t₀) = ker A_{t₀}^b` for every smooth
   representation, and the compression of `t₀` splits.
3. **Compact sets.** `N(F)` and `N̄(F)` are closed (`isClosed_pointImage_comp`), so
   `K ∩ N(F)` and `K ∩ N̄(F)` are compact. Put
   `C = t₀^{-b} (K ∩ N(F)) t₀^b` and `C̄ = t₀^b (K ∩ N̄(F)) t₀^{-b}`. These are continuous
   images of compact sets, hence compact. They lie in `N(F)` and `N̄(F)` because
   `t₀ ∈ M(F)` normalizes both (`pointImage_le_normalizer`, together with
   `mbar ≫ pbar = m ≫ p` for `N̄`). These are Renard's `C` and `C̄` from Remark 2.
4. **Contraction.** Apply `SplitComponentOppositeContractionStatement` to `C`, `C̄` and the
   neighbourhood `L = K` of `1` to get `ε`. Fix `t` with `|α(t)| < ε` for `α ∈ Δ` and put
   `g = incG t`. Then `g (t₀^{-b} u t₀^b) g⁻¹ ∈ K` for `u ∈ K ∩ N(F)`, and
   `g⁻¹ (t₀^b l t₀^{-b}) g ∈ K` for `l ∈ K ∩ N̄(F)`. These are Renard's inclusions
   `C ⊂ t^{-1} K_N t` and `C̄ ⊂ t K_{N̄} t^{-1}`. In the language of the helper module,
   `g` dominates `t₀ ^ b`.
5. **Centrality.** `g = rationalPoints.map (m ≫ p) (rationalPoints.map a t)` lies in `M(F)`.
   It commutes with `M(F)` by the Library `splitComponent_point_comm`, because the split
   component is central.
6. **Conclusion.** By `Jacquet.IsIwahoriContraction.of_dominates`, `g` is an `M(F)`-central
   Iwahori contraction. Step 1 then shows that the compression of `g` splits.
   `Jacquet.ker_range_compressedAction_of_dominates` now gives `V^K_0(t₀) = ker A_g` and
   `V^K_*(t₀) = Im A_g`, which is the target's conclusion.

The helper module `Langlands.Representation.Jacquet.DominatedIwahoriContraction` explains
steps 4–6 at the level of abstract groups. Its route differs from Renard's. Renard compares
`A_t` with the averages `e_{t^{-1} K_N t}` and `e_{C̄}` of Remark 2. Here we use the
factorizations `A_g = A_Y ∘ A_{t₀}^b = A_{t₀}^b ∘ A_Y` with `Y = t₀^{-b} g`, the Library
identification of kernel suprema with the kernel of the Jacquet map, and the splitting
for `g`.
