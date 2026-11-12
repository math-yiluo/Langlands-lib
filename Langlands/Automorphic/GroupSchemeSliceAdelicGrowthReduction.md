# Slice-wise growth gives full adelic growth under rational height reduction

Author: Worker 5152.

This module proves that
`Langlands.Global.RepresentationGrowth.AdelicRationalHeightReductionStatement`
(module `AdelicRationalHeightReductionStatement`) implies the published target
`Langlands.Automorphic.GroupSchemeFunctions.AdelicSliceModerateGrowthStatement`
(module `GroupSchemeSliceAdelicGrowthStatement`), universe by universe. It does not
prove either proposition. The reduction statement contains the reduction theory:
class-number finiteness and Mœglin–Waldspurger I.2.1 and I.2.2 (vii). It is still
unproved, so the slice-to-global comparison remains open.

## Main result

```lean
theorem adelicSliceModerateGrowthStatement_of_rationalHeightReduction
    (hred : RepresentationGrowth.AdelicRationalHeightReductionStatement.{u}) :
    AdelicSliceModerateGrowthStatement.{u}
```

The hypothesis is the reduction proposition at the same universe `u`. The
conclusion is the unchanged target at its full scope. Every number field `F`, every
affine group scheme `G` over `F`, every closed matrix representation `rho` with
`0 < N` and every continuous rational-invariant `f` with an open finite stabilizer
and polynomially bounded infinite slices has `HasAdelicModerateGrowth F G rho f`.
The proof adds no hypothesis on `F`, `G`, `rho` or `f`.

## Proof

Fix `F`, `G`, `rho`, the three structural hypotheses and `f`. The reduction
statement, applied to the same `F`, `G` and `rho`, gives a compact
`Ω ⊆ G(𝔸_f)`, a constant `C > 0` and an exponent `e`. For each `g` it gives a
rational `q` with `x = rational(q) g` such that `x_f ∈ Ω` and
`height(x_∞) ≤ C · adelicHeight(g)^e`.

1. **Finitely many cosets.** Membership of `f` in `finiteSmoothSubrepresentation`
   gives an open subgroup `L` of `G(𝔸_f)` with
   `finiteRightAction F G l f = f` for every `l ∈ L`. The helper
   `exists_finset_mem_leftCoset` covers `Ω` by finitely many left cosets. For any
   topological group with continuous multiplication, an open subgroup `L` and a
   compact `Ω`, there is a finite set `B` such that every `x ∈ Ω` has some `b ∈ B`
   with `b⁻¹ x ∈ L`. The proof applies `IsCompact.elim_finite_subcover` to the open
   cover of `Ω` by the cosets `{y | b⁻¹ y ∈ L}`, `b ∈ Ω`.
2. **Finitely many slice bounds.** The slice hypothesis
   `GroupSchemeFunctions.HasPolynomialGrowth F G rho f` gives, for each finite
   point `b`, constants `K_b ≥ 0` and `d_b ∈ ℕ` with
   `‖f(pair a b)‖ ≤ K_b · height(a)^{d_b}` for all infinite points `a`. Put
   `K₀ = ∑_{b ∈ B} K_b` and `D = max_{b ∈ B} d_b` (`Finset.sup`).
3. **Reduction of one value.** Let `g` be an adelic point. Take `q` and `x` as
   above, and choose `b ∈ B` with `b⁻¹ x_f ∈ L`.
   - `evaluate_rational_mul` gives `f(x) = f(g)`. This is the defining invariance
     of the rational-invariant functions, `Representation.coindV` with trivial
     coefficients.
   - `evaluate_eq_infiniteSlice_of_mem` gives
     `f(x) = infiniteSlice F G b f (x_∞) = f(pair x_∞ b)`. It writes
     `x = pair x_∞ x_f = pair x_∞ b · ofFinite(b⁻¹ x_f)` and uses the
     `L`-invariance of `f`, through `pair_projections`, `pair_mul` and
     `ofFinite_eq_pair`.
4. **The estimate.** Since `1 ≤ height(x_∞)`, `b ∈ B` and `K_b ≥ 0`,
   ```text
   ‖f(g)‖ = ‖f(pair x_∞ b)‖ ≤ K_b height(x_∞)^{d_b} ≤ K₀ height(x_∞)^D
          ≤ K₀ (C adelicHeight(g)^e)^D = (K₀ C^D) adelicHeight(g)^{D e}.
   ```
   So `f` satisfies `HasAdelicPolynomialGrowth` with the nonnegative constant
   `K₀ C^D` and the exponent `D e`. The published
   `hasAdelicModerateGrowth_iff F G rho hN f` (module `GroupSchemeAdelicGrowth`)
   converts this to `HasAdelicModerateGrowth`, with `0 < N` used for the lower
   bound of the source norm.

The proof uses neither reductivity nor the closed embedding directly; both are
passed to the reduction statement.

## Helper declarations

- `exists_finset_mem_leftCoset`: a compact set meets only finitely many left cosets
  of an open subgroup (step 1). It is stated for an arbitrary group with a topology
  and continuous multiplication.
- `evaluate_rational_mul`: `evaluate F G f (rational q * g) = evaluate F G f g`.
- `evaluate_eq_infiniteSlice_of_mem`: if `L` fixes `f` and `b⁻¹ x_f ∈ L`, then
  `evaluate F G f x = infiniteSlice F G b f x_∞`.

## Relation to the target's proof sketch

The target's Markdown sketches the argument: Siegel covering, finitely many slices,
height comparison and MW I.2.2 (vii). This module does the "finitely many slices"
step and the final combination. The covering, the norm minimality and the height
comparison are bundled into the single proposition
`AdelicRationalHeightReductionStatement`. Its Markdown explains how that
proposition follows from the Siegel covering `AdelicSiegelReductionStatement`, the
norm-one decomposition and MW I.2.2 (vii).
