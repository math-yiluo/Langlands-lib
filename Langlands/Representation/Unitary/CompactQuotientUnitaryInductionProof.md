# Unitarity of normalized induction from a cocompact closed subgroup: proof

Author: Worker 32.

The theorem `Langlands.Renard.CompactRepresentation.compactQuotientUnitaryInduction`
(universe parameters `uG`, `v`) proves the unchanged published proposition
`Langlands.Renard.CompactRepresentation.CompactQuotientUnitaryInductionStatement`
(module `Langlands.Representation.Unitary.CompactQuotientUnitaryInductionStatement`). It
adds no hypothesis. The source assertion is Renard 2026, IV.2.3 "Induction des
représentations unitaires", printed pp.98–99 / PDF pp.104–105, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The Lean proof follows
the source's argument. It also proves two facts the source uses without proof: a nonzero
positive invariant functional is strictly positive, and some such functional exists.

The module imports the target statement, `Langlands.Representation.Unitary.RelativeQuotientMeasure`
(the measure used for part 2), `Langlands.Representation.Induction.CompactIntegralForm`
(local constancy of the pointwise pairing) and `Langlands.Topology.CompactOpen.NeighborhoodBasis`
(compact open subgroups). All declarations other than the final theorem are internal proof
infrastructure.

## Generic lemmas on `space H χ`

Namespace `Langlands.HarmonicAnalysis.HomogeneousFunctions.PositiveFunctional`. Here `G` is a
topological group, `H` a subgroup and `χ : H →* ℝ≥0`. The space `space H χ` consists of
locally constant `f : G → ℂ` with `f(h x) = χ(h) f(x)` and support in `H K` for some compact
`K`. `renardSpace H hH` is this space for `χ = relativeModular H hH`.

- `pointwise Φ hΦ f` applies a map `Φ : ℂ → ℂ` pointwise to `f`. If `Φ(r z) = r Φ(z)` for
  every real `r ≥ 0`, the result stays in `space H χ`: covariance holds because the values
  of `χ` are nonnegative reals, and the support can only shrink because `Φ(0) = 0`.
  Instances: `rePart`, `imPart`, `normPart` and `conjPart`, which take the real part, the
  imaginary part (each as a complex number), the absolute value and the complex conjugate.
  `re_add_im` gives `ψ = rePart ψ + i · imPart ψ` and `conjPart_eq` gives
  `conjPart ψ = rePart ψ − i · imPart ψ`.
- `IsNonneg f` means every value of `f` is a real number `≥ 0`. This is the positivity
  hypothesis of the target statement.
- `sandwich`: let `ν` be positive, meaning `ν f` is real and `≥ 0` whenever `IsNonneg f`.
  If `ψ` and `M` are real-valued and `|ψ(x)| ≤ M(x)` pointwise, then `ν ψ` is real and
  `|ν ψ| ≤ Re ν M`. Proof: apply positivity to `M + ψ` and `M − ψ`.
- `im_apply_rePart` and `im_apply_imPart`: `ν` is real on `rePart ψ` and on `imPart ψ`.
  This is `sandwich` with `M = normPart ψ`. Then `apply_conjPart` gives
  `ν (conjPart ψ) = conj (ν ψ)`: write `ψ = rePart ψ + i · imPart ψ` and use linearity.
- `exists_dominating`: let `F` be nonnegative with `F(x₀) ≠ 0`. Then for every `ψ` there are
  `C ≥ 0` and a finite set `s ⊆ G` such that `‖ψ(x)‖ ≤ C ∑_{g ∈ s} Re F(x g)` for all `x`.
  Proof: take a compact `K` with `supp ψ ⊆ H K`. The open sets
  `{y | F(y g) = F(x₀)}` for `g ∈ G` cover `K` (for `k ∈ K` use `g = k⁻¹ x₀`); choose a
  finite subcover indexed by `s`. Let `S` bound `‖ψ‖` on `K`, and take
  `C = max(S, 0) / Re F(x₀)`, where `Re F(x₀) > 0`. For `x = h k` with `h ∈ H` and `k ∈ K`,
  pick `g ∈ s` with `F(k g) = F(x₀)`. Covariance of `ψ` and `F` gives
  `‖ψ(h k)‖ = χ(h) ‖ψ(k)‖ ≤ χ(h) max(S, 0) = C · Re F(h k g)`, which is at most the sum.
  Outside the support the bound is trivial.
- `eq_zero_of_apply_eq_zero` and `apply_ne_zero`: let `ν` be positive and invariant under
  right translation. If `F` is nonnegative, `F(x₀) ≠ 0` and `ν F = 0`, then `ν = 0`. Proof:
  fix `ψ` and let `M = C ∑_{g ∈ s} rightAction g F`, which is real. Invariance gives
  `ν M = 0`. `sandwich` applied to `rePart ψ` and to `imPart ψ`, both bounded by `M`
  through `exists_dominating`, gives `ν (rePart ψ) = ν (imPart ψ) = 0`, so `ν ψ = 0`.
  Contrapositively, a nonzero positive invariant `ν` does not vanish on any nonnegative
  `F ≠ 0`. This is the strict positivity that the statement's faithfulness notes leave to
  the proof.

## The pairing and the form

Namespace `Langlands.Renard.CompactRepresentation.UnitaryInduction`. Here `G` is
nonarchimedean and locally compact, `H` is closed and `H \ G` is compact.

- `relativeModular_eq` shows that `relativeModular H hH h` equals the positive-unit relative
  modulus `relativePositiveModulus H h` (module `Unitary/RelativeHalfModulus`). It unfolds
  both and uses `renardModular_eq_inv` (Renard's modular function is the inverse of
  Mathlib's modular character). This is the agreement of the two published forms of
  `δ_{H\G}` mentioned in the statement's Markdown.
- `exists_compact_cover` gives a compact `K` with `G = H K`. Take a compact open subgroup
  `K₀` (`compactOpenSubgroupBasis`) and a finite set `t` with `G = ⋃_{i ∈ t} H i K₀`
  (`exists_finset_doubleCoset_cover`, module `Induction/CompactQuotientProof`), and set
  `K = t K₀`.
- `core_inner_smul_right`: `b(v, c w) = c b(v, w)` for an `InnerProductSpace.Core`.
- `pairing H hH ρ b hcov f₁ f₂` is the function `x ↦ b(f₁(x), f₂(x))` (IV.2.3.2) as an
  element of `renardSpace H hH`, for any representation `ρ` of `H` whose form `b` satisfies
  `b(ρ(h) v, ρ(h) w) = δ_{H\G}(h) b(v, w)` (`hcov`). Local constancy is the published
  `pairing_isLocallyConstant`. Covariance follows from `eval_covariant` and `hcov`. The
  support condition holds with the compact set from `exists_compact_cover`, since
  `H K = G`.
- `pairing_add_left`, `pairing_smul_left`, `pairing_swap` (swapping the arguments gives
  `conjPart` of the pairing), `pairing_translate` (translating both functions by `g`
  translates the pairing by `g`), `pairing_self_nonneg` (the pairing of `f` with itself is
  nonnegative) and `pairing_self_ne_zero` (if `f ≠ 0` its self-pairing is nonzero at some
  point, by definiteness of `b`). Each is checked pointwise.
- `formOfFunctional` builds an `InvariantPositiveForm (compactInduced H ρ)` with inner
  product `ν (pairing f₁ f₂)` (IV.2.3.1). It takes a linear functional `ν` that is invariant,
  positive, and strictly positive (nonzero on every nonnegative element that is nonzero at
  some point). Hermitian symmetry comes from `pairing_swap` and `apply_conjPart`.
  Additivity and conjugate-linearity in the first variable come from linearity of `ν`.
  Positivity is `hpos` applied to the self-pairing. Definiteness: if `f ≠ 0`, its
  self-pairing is nonnegative and nonzero at some point, so its `ν`-value is nonzero by
  strict positivity. Invariance comes from `pairing_translate` and invariance of `ν`.

## Existence of a functional

`exists_invariantFunctional`, for `G` Hausdorff with `[LocallyCompactSpace H]`, constructs
a linear functional on `renardSpace H hH` that is invariant, positive and strictly positive.
The proof installs the Borel σ-algebra on `G` locally (`borelize G`). This adds no hypothesis
to the target. It then takes the measure `μ` on `⊤ : Subgroup G` from the published
`Langlands.Induction.exists_compactQuotient_relativeMeasure` (module
`Unitary/RelativeQuotientMeasure`). `μ` is positive on open neighbourhoods of `1`. For every
locally constant `φ` that is covariant for `relativePositiveModulus`, the functions
`k ↦ φ(k g)` are `μ`-integrable and their integral does not depend on `g`. By
`relativeModular_eq`, every element of `renardSpace H hH` is such a `φ`. Set
`ν f = ∫ f(k) dμ(k)`:

- linearity follows from linearity of the Bochner integral;
- invariance is the independence of `g`;
- positivity: for nonnegative `f` the imaginary part of the integral is `∫ 0 = 0`, and its
  real part is the integral of a nonnegative function;
- strict positivity: let `f` be nonnegative, `f(x₀) ≠ 0` and `ν f = 0`. By invariance
  `∫ Re f(k x₀) dμ = 0`, so `Re f(k x₀) = 0` for `μ`-almost every `k`. The set
  `U = {k | f(k x₀) = f(x₀)}` is open, because `f` is locally constant, and contains `1`. On
  `U` the integrand equals `Re f(x₀) > 0`, so `μ U = 0`. This contradicts positivity of `μ`
  on open neighbourhoods of `1`.

This functional replaces Renard's `ν_{H\G}` from II.3.9. The proof does not use the
unproved `InvariantFunctionalStatement`.

## The main theorem

`compactQuotientUnitaryInduction` introduces the data of the statement, including
`σ = twist χ τ`. It proves three facts:

- `hδ`: `χ(h) χ(h) = δ_{H\G}(h)` as complex numbers. This comes from the hypothesis
  `χ(h)² = relativeModularCharacter(h)`, rewritten with `complexCharacter_relativePositiveModulus`
  and `relativeModular_eq`.
- `hreal`: `conj χ(h) = χ(h)`, because `χ(h)` is a positive real number by hypothesis.
- `hcov`: `b(σ(h) v, σ(h) w) = δ_{H\G}(h) b(v, w)`. Expand
  `σ(h) = χ(h) τ(h)`, then use sesquilinearity of `b`, invariance of `b` under `τ`, `hreal`
  and `hδ`.

Part 1 takes `c = pairing H hH σ b hcov`; its value formula holds by definition. For a
nonzero, invariant, positive `ν`, the form is `formOfFunctional` with strict positivity
supplied by `apply_ne_zero`, and `B.inner f₁ f₂ = ν (c f₁ f₂)` holds by definition. Part 2,
`IsUnitarizable π`, is `formOfFunctional` applied to the functional from
`exists_invariantFunctional`. Here `π = normalizedCompactInduced H χ τ.representation` is by
definition `compactInduced H σ`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
