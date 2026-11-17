# Contracting powers for compact open subgroups with an Iwahori decomposition: proof

Author: Worker 59.

Module: `Langlands.Representation.Exponents.RepresentedIwahoriContractionProof`.

This module proves the proposition
`Langlands.Aubert.General.RepresentedParabolic.RepresentedIwahoriContractionStatement.{u}`
(module `Langlands.Representation.Exponents.RepresentedIwahoriDecompositionStatements`) as

```text
Langlands.Aubert.General.RepresentedParabolic.representedIwahoriContraction :
  RepresentedIwahoriContractionStatement.{u}
```

The statement is the derived first step of the proofs of Renard 2026, VI.6.1 Théorème
(printed p.176 / PDF p.182) and VI.9.1 Théorème (printed p.195 / PDF p.201): "on choisit
alors `t ∈ C_A^{++}`". Its own Markdown explains this provenance. The proof adds no
hypothesis. It keeps the field universe `u`, the canonical point topology, the actual maps
`p`, `m`, `n`, `pbar`, `mbar`, `nbar`, the compact open subgroup `K` with its ordered
decomposition `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))`, the split component `a` and the
compatible presentation `pres` exactly as the statement gives them. The instances
`LocallyCompactSpace` and `NonarchimedeanGroup` are only passed on to the published
`splitComponentOppositeContraction`. Only the axioms `propext`, `Classical.choice` and
`Quot.sound` are used.

Notation: `Δ` and `incG` are the `let`-bound set of restricted simple roots and the map
`rationalPoints.map (a ≫ m ≫ p) : A(F) →* G(F)` of the statement. "Norm" means
`CocharacterUniformizer.characterNorm k A`. `N(F)`, `M(F)` and `N̄(F)` stand for the
subgroups `pointImage (n ≫ p)`, `pointImage (m ≫ p)` and `pointImage (nbar ≫ pbar)` of
`G(F)`.

## Helper lemmas (namespace `...RepresentedParabolic.IwahoriContractionPowers`)

These are elementary facts about the norm of a character on powers of one point
`t ∈ A(F)`.

- `characterNorm_pow`: the norm of `α` at `t ^ j` is the `j`-th power of its norm at `t`.
  The norm is a monoid homomorphism in the point, so `simp` with `map_pow` closes it.
- `characterNorm_nonneg`: the norm is nonnegative, since it is the coercion of an `NNReal`.
- `exists_pow_characterNorm_lt`: for a finite set `Δ` of characters with norm `< 1` at
  `t` and any `ε > 0`, there is `j₀` such that for every `j ≥ j₀` every `α ∈ Δ` has norm
  `< ε` at `t ^ j`. For each `α`, the sequence of norms at `t ^ j` is the geometric sequence
  `‖α(t)‖ ^ j`, which tends to `0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`). Hence it is
  eventually `< ε`. `Filter.eventually_all_finite` combines the finitely many roots, and
  `Filter.eventually_atTop` turns the result into an explicit `j₀`.
- `characterNorm_pow_lt_one`: if every `α ∈ Δ` has norm `< 1` at `t`, the same holds at
  `t ^ r` for every `r ≠ 0` (`pow_lt_one₀`).

## Main proof

After introducing the data, the proof installs the instances `IsAffineHom G.X.hom`,
`Smooth G.X.hom` (both from `hG`) and the point topology on `G(F)`. The set `Δ` is finite
because it is the image of a subset of the finite set of simple roots
(`pres.finite_simpleRoots`).

### Part (i): a point of `A^{++}`

Let `μ = pres.splitComponentCocharacter` be the chosen cocharacter of `A` that defines `P`
(module `Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter`). The witness is
`t₀ = CocharacterUniformizer.latticeSection k A (ofAdd μ)`, the value of `μ` at the
uniformizer. Let `α = f ≫ β` be an element of `Δ`, where `β` is a simple root outside `J`.
By `RelativeRoot.latticePairing_restrict_cocharacterMapInt`, the pairing `⟨f ≫ β, μ⟩` equals
`⟨β, f_* μ⟩`. This is positive by the third clause of
`pres.isStandard_splitComponentCocharacter`: the image `f_* μ` of `μ` in the presentation
torus is a standard cocharacter, and it pairs positively with every simple root outside `J`.
`CocharacterUniformizer.characterNorm_latticeSection_lt_one` turns a positive pairing into
norm `< 1`.

### Part (ii): contracting powers

Fix `t₀` with every `α ∈ Δ` of norm `< 1` at `t₀`.

1. **Compact pieces.** `K ∩ N(F)` and `K ∩ N̄(F)` are compact. Each is the intersection of
   the compact set `K` with a closed set; the images of `N(F)` and `N̄(F)` are closed by
   `isClosed_pointImage_comp` (this uses `[T2Space k]` and the closed-subgroup fields of
   `hp`, `hn`, `hpbar`, `hnbar`).
2. **The two-sided contraction theorem.** Let `hcontr` be the published
   `splitComponentOppositeContraction` applied to the given data. For compact
   `C ⊆ N(F)`, compact `C̄ ⊆ N̄(F)` and a neighbourhood `L` of `1`, it gives `ε > 0` such
   that, for every `t ∈ A(F)` with all norms on `Δ` below `ε`, `incG t` conjugates `C` into
   `L` and `(incG t)⁻¹` conjugates `C̄` into `L`.
3. **Facts about `incG s`.** `incG s` equals `rationalPoints.map (m ≫ p)` applied to
   `rationalPoints.map a s` (`pointMap_comp_apply`). So it lies in `M(F)`, and it commutes
   with every element of `M(F)` (`splitComponent_point_comm`, which uses that `A` is a
   central torus of `M`). `M(F)` normalizes `N(F)` (`pointImage_le_normalizer p m n hn`).
   It also normalizes `N̄(F)`: rewrite `M(F)` as `pointImage (mbar ≫ pbar)` using
   `mbar ≫ pbar = m ≫ p`, and apply `pointImage_le_normalizer pbar mbar nbar hnbar`.
4. **Choice of `r₀`.** Apply `hcontr` with `C = K ∩ N(F)`, `C̄ = K ∩ N̄(F)` and `L = K`
   (a neighbourhood of `1` because `K` is open). This gives `ε`.
   `exists_pow_characterNorm_lt` then gives `r₁` such that `t₀ ^ r` has all norms on `Δ`
   below `ε` for every `r ≥ r₁`. Put `r₀ = max r₁ 1`. Fix `r ≥ r₀` and write
   `g = incG (t₀ ^ r)`. Then `r ≠ 0`, so `t₀ ^ r` again has all norms on `Δ` below `1`
   (`characterNorm_pow_lt_one`), and `g` conjugates `K ∩ N(F)` into `K` while `g⁻¹`
   conjugates `K ∩ N̄(F)` into `K`.
5. **The seven fields of `Jacquet.IsIwahoriContraction`.**
   - `mem_levi`: step 3.
   - `factor`: the decomposition hypothesis on `K`, unchanged.
   - `upper`: for `u ∈ K ∩ N(F)`, `g u g⁻¹` lies in `K` by step 4. It lies in `N(F)` because
     `g ∈ M(F)` normalizes `N(F)`.
   - `levi`: for `y ∈ K ∩ M(F)`, `g⁻¹ y g = y` because `g` commutes with `y` (step 3).
   - `lower`: for `l ∈ K ∩ N̄(F)`, `g⁻¹ l g` lies in `K` by step 4. It lies in `N̄(F)` because
     `g⁻¹ ∈ M(F)` normalizes `N̄(F)`; the normalizer criterion gives
     `g⁻¹ l (g⁻¹)⁻¹`, and `inv_inv` rewrites it.
   - `exhaust`: let `x ∈ N(F)`. Apply `hcontr` with `C = {x}`, `C̄ = ∅` and `L = K`. This
     gives `ε'`, and `exists_pow_characterNorm_lt` applied to the point `t₀ ^ r` (whose norms
     on `Δ` are `< 1`) gives `s` with all norms on `Δ` at `(t₀ ^ r) ^ s` below `ε'`. Since
     `incG` is a homomorphism, `g ^ s = incG ((t₀ ^ r) ^ s)` (`map_pow`), so
     `g ^ s x (g ^ s)⁻¹ ∈ K`.
   - `contract`: let `L` be an open subgroup of `G(F)`. Apply `hcontr` with `C = ∅`,
     `C̄ = K ∩ N̄(F)` and the neighbourhood `L`. As for `exhaust`, this gives `s` with
     `(g ^ s)⁻¹ l g ^ s ∈ L` for every `l ∈ K ∩ N̄(F)`.

The hypotheses `IsIso (subgroupMultiplication m n)`, `IsIso (subgroupMultiplication mbar nbar)`
and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)` are used only through
`splitComponentOppositeContraction`, which takes them.

## Relation to the literature

Renard picks `t ∈ C_A^{++}` and uses V.5.2 (iii) for the contraction. In this proof, the
existence of such a point comes from the uniformizer value of the defining cocharacter, and
the contraction estimates come from the published two-sided form of V.5.2 (iii),
`splitComponentOppositeContraction`. The only extra argument is that powers of a fixed
point of `A^{++}` eventually have all norms on `Δ` below any given `ε`.
