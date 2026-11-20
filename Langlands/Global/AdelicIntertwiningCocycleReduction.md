# Reduction of the cocycle relation of intertwining operators

Module `Langlands.Global.AdelicIntertwiningCocycleReduction` states and proves a
reduction of the Library's `Langlands.Global.IntertwiningCocycleStatement`
(Bernstein–Lapid, Theorem 2.3 (5); module
`Langlands.Global.AdelicIntertwiningCocycleStatement`) to four statements.
Worker 86 wrote it for Task 5503, whose target is that statement. The module
does not prove the cocycle relation outright: the four statements remain
premises.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §8.6, journal
p.225 (PDF page 39): for `w ∈ W(P, P')` and `w' ∈ W(P', P'')`,

`E(M(w'w, λ)φ, w'wλ) = E(φ, λ) = E(M(w, λ)φ, wλ) = E(M(w', wλ)M(w, λ)φ, w'wλ)`

by the functional equation (Theorem 2.3 (4)), and therefore
`M(w'w, λ) = M(w', wλ)M(w, λ)` by (8.4), the generic injectivity of
`φ ↦ E(φ, λ)` on finite-dimensional subspaces of automorphic forms. The Lean
proof follows this argument. The work lies in making the continuations,
domains and finite-dimensional spaces explicit.

## Declarations

All declarations are in the namespace `Langlands.Global`, universe `u`.

- `IntertwiningCocycleReductionStatement : Prop` is the implication
  `EisensteinFunctionalEquationStatement.{u} →
  IntertwiningMeromorphicContinuationStatement.{u} →
  EisensteinPointwiseContinuationStatement.{u} →
  EisensteinGenericInjectivityStatement.{u} →
  IntertwiningCocycleStatement.{u}`.
- `intertwiningCocycle_of_inputs (hFE) (hIC) (hPC) (hGI) :
  IntertwiningCocycleStatement.{u}` is the proof, with the four premises as
  hypotheses.
- `intertwiningCocycleReduction : IntertwiningCocycleReductionStatement.{u}`
  restates that theorem in the form of the proposition.

The premises:

- (FE) `EisensteinFunctionalEquationStatement` (Library, module
  `Langlands.Global.AdelicEisensteinFunctionalEquationStatement`):
  BL Theorem 2.3 (4), universal in the continuations.
- (IC) `IntertwiningMeromorphicContinuationStatement` (Library, module
  `Langlands.Global.AdelicIntertwiningContinuationStatement`): BL
  Theorem 2.3 (3). For `φ ∈ 𝒜_P` there are finitely many `ψ i ∈ 𝒜_Q` and
  meromorphic coefficients with `M(w, λ)φ = ∑ i, coeff i λ · ψ i` for `λ`
  regular.
- (PC) `EisensteinPointwiseContinuationStatement` (new, module
  `Langlands.Global.AdelicEisensteinPointwiseContinuationStatement`): BL
  Theorem 2.3 (1) for finite families, evaluated at points, with one common
  domain of holomorphy.
- (GI) `EisensteinGenericInjectivityStatement` (new, module
  `Langlands.Global.AdelicEisensteinGenericInjectivityStatement`): BL (8.4)
  for any pointwise continuations, on an open dense set in each chart.

The Markdown files of the two new modules give their sources and
correspondence.

The other declarations are private helper lemmas, described below.

## Proof of `intertwiningCocycle_of_inputs`

Take the data of the cocycle statement (see its Markdown):

- the parabolics `P`, `Q` with presentations `r`, `r'`, and `Q''`;
- `(w, c)` and `(w', c')`, and `K` with `hK`, `hK'`, `hK''`;
- `φ ∈ 𝒜_P`;
- the given expansions `M(w, λ)φ = ∑ i, coeff i λ · ψ i` (domain `D`),
  `M(w', μ)(ψ i) = ∑ j, coeff' i j μ · χ j` (domain `D'`) and
  `M(w'w, λ)φ = ∑ j, coeff'' j λ · χ'' j` (domain `D''`);
- `λ₀ ∈ D ∩ D''` with `wλ₀ ∈ D'`, and `g₀ ∈ G(𝔸)`.

Write `wλ = weylParameter l c π' λ` and
`(w'w)λ = weylParameter l (c' ≫ c) π'' λ`.

The given functions `χ j` and `χ'' j` need not be automorphic, so (FE)
cannot be applied to the given expansions directly. The proof therefore
builds automorphic expansions with (IC), proves the relation for those, and
transfers it back in step 8.

1. **Weyl parameters.** `wλ` and `(w'w)λ` are complex linear equivalences
   `We`, `We''` (helper `exists_weylParameter_linearEquiv`: restriction
   `X^*(P) → X^*(M)` along a rational Levi is bijective, `c^*` is bijective,
   and composition with `π'` inverts restriction along `l'`). Moreover
   `weylParameter l' c' π'' (wλ) = (w'w)λ`. The proof checks this on pure
   tensors, using `l' ≫ π' = 𝟙 M'`.
2. **The composite element.** `IsWeylConjugation p l q'' l'' (w' * w)
   (c' ≫ c)` holds: `c' ≫ c` is an isomorphism, and
   `(c' ≫ c) ≫ l ≫ p = l'' ≫ q'' ≫ (innerIso (w' * w)).inv`. This follows
   from the two given conjugation identities and
   `innerIso (w' * w) = innerIso w ≪≫ innerIso w'` (Library lemma
   `GroupScheme.innerIso_mul_hom`). This is the derivation sketched in the
   Markdown of the cocycle statement.
3. **A presentation of `Q''`.** `a'' := a' ≫ c'⁻¹ : A' → M''` is a split
   component of `M''` (`IsSplitComponent.comp_iso`). The Library theorem
   `parabolicRootPresentationExistence` gives a presentation
   `r'' : ParabolicRootPresentation q'' l'' a''`. Its auxiliary instances
   follow from the compatibility fields of `r''`:
   - `r''.data.i` is mono;
   - the relative Weyl group is finite (`finite_relativeWeylGroup`);
   - the group homomorphism of `r''.data.f` is mono.
4. **Continuations and expansions.**
   - (PC) for `P` and the single form `φ` gives `EP` with domain `DP`.
   - (PC) for `Q` and the family `ψ` gives `EQ` with domain `DQ`.
   - (IC) for `(P → Q'', w' * w, c' ≫ c)` and `φ` gives automorphic forms
     `ψ₁ b ∈ 𝒜_{Q''}` and coefficients `c₁ b` (domain `D₁`) with
     `M(w'w, λ)φ = ∑ b, c₁ b λ · ψ₁ b` for `λ` regular.
   - (IC) for `(Q → Q'', w', c')` and each `ψ i` gives `ψ₂ i b ∈ 𝒜_{Q''}` and
     `c₂ i b` (domain `D₂ i`).
   - (PC) for `Q''` with `r''` and the combined family
     `ψ'' = Sum.elim ψ₁ (fun x => ψ₂ x.1 x.2)`, indexed by
     `Fin k₁ ⊕ Σ i, Fin (k₂ i)`, gives `E''` with domain `DC`.
5. **Domains.** A family indexed by `Idx` with common domain `S` is used with
   the domain `⋂ _ : Idx, S`: this is `S` when `Idx` is nonempty and the
   whole space when `Idx` is empty. Such a set is open and dense in every
   chart even when the family is empty and nothing is known about `S`
   (helper `isMeromorphicInCoordinatesOn_iInter_const`). In what follows a
   primed domain such as `DQ'` stands for `⋂ _ : Idx, DQ` over the
   appropriate index type.
6. **Three functional equations.** (FE) is applied three times:
   - (FE1) to `(P → Q'', w' * w)`, `φ`, `EP` and the expansion
     `(ψ₁, c₁)`: `EP λ = ∑ b, c₁ b λ · E''(inl b)((w'w)λ)`;
   - (FE2) to `(P → Q, w)`, `φ`, `EP` and the given expansion
     `(ψ, coeff)`: `EP λ = ∑ i, coeff i λ · EQ i (wλ)`;
   - (FE3) for each `i`, to `(Q → Q'', w')`, `ψ i`, `EQ i` and the expansion
     `(ψ₂ i, c₂ i)`: `EQ i μ = ∑ b, c₂ i b μ · E''(inr ⟨i, b⟩)(w'μ)`.

   Each holds pointwise on the stated domains. Let
   `Θ = DP ∩ D₁' ∩ D ∩ We⁻¹(DQ' ∩ ⋂ i, D₂ i') ∩ We''⁻¹ DC'`. It is open and
   dense in every chart (helpers `OpenDenseInCoordinates.inter`, `.preimage`
   and `.iInter`).
7. **The relation in `𝒜_{Q''}` (`hstar0`, `hstar`).** For `λ ∈ Θ`,
   substitute (FE3) at `μ = wλ` into (FE2), using `w'(wλ) = (w'w)λ`, and
   subtract (FE1). This gives `∑ x, C x · E'' x ((w'w)λ) = 0` for the
   coefficients `C (inl b) = c₁ b λ` and
   `C (inr ⟨i, b⟩) = −coeff i λ · c₂ i b (wλ)`. Now fix the chart
   `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` given by a basis. (GI), applied on `Q''` to the
   family `ψ''`, the continuations `E''` and the chart `We'' ∘ e`, gives an
   open dense `O ⊆ ℂⁿ`. For `s ∈ O` with `e s ∈ Θ`, it turns the relation
   into `∑ x, C x · ψ'' x = 0`, that is,

   `∑ b, c₁ b (e s) · ψ₁ b = ∑ i, coeff i (e s) · ∑ b, c₂ i b (w(e s)) · ψ₂ i b`

   as functions on `G(𝔸)`.
8. **Transfer to the given expansions.** For fixed `g₀`:
   - `λ ↦ ∑ j, coeff'' j λ · χ'' j g₀` and `λ ↦ ∑ b, c₁ b λ · ψ₁ b g₀` are
     meromorphic. Both equal `M(w'w, λ)φ (g₀)` for `λ` regular enough (take
     the larger threshold, `regularParameter_mono`). So they agree on the
     intersection of their domains (`hT1`).
   - Likewise, for each `i`, `μ ↦ ∑ j, coeff' i j μ · χ j g₀` and
     `μ ↦ ∑ b, c₂ i b μ · ψ₂ i b g₀` agree on the intersection of their
     domains (`hT2`).

   Both use the helper `eqOn_of_regular`. In a chart, the region
   `r.IsRegularParameter hA hT R` is defined by finitely many strict real
   linear inequalities, so it is open, and it is nonempty. Two meromorphic
   functions agreeing on a nonempty open set agree on the intersection of
   their domains.
9. **Conclusion.** Let `F₁ λ = ∑ j, coeff'' j λ · χ'' j g₀`, meromorphic on
   `⋂ _ : Fin k'', D''`. Let
   `F₂ λ = ∑ i, coeff i λ · ∑ j, coeff' i j (wλ) · χ j g₀`, meromorphic on
   `⋂ _ : Fin k, (D ∩ We⁻¹(⋂ _ : Fin k', D'))`. The required meromorphy
   facts are products, finite sums and composition with the linear
   equivalence `We`. On the part of `O ∩ e⁻¹Θ` inside both domains,
   `F₁ ∘ e = F₂ ∘ e` by steps 7 and 8. The set `O ∩ e⁻¹Θ` is open and
   nonempty, since it is the intersection of two open dense sets. By the
   identity theorem (`IsMeromorphicInCoordinatesOn.eqOn_of_eqOn_open`),
   `F₁ = F₂` on the intersection of the two domains. The hypotheses
   `λ₀ ∈ D ∩ D''` and `wλ₀ ∈ D'` put `λ₀` in it, which is the conclusion of
   `IntertwiningCocycleStatement` at `(λ₀, g₀)`.

## Helper lemmas

The private sections reproduce helper lemmas written by Worker 587 in their
draft for Task 5502 (the functional equation). They are copied here as
private declarations, in the original namespaces so that dot notation works.
If the originals are published later, the names do not clash.

- *Scalar meromorphic functions* (`Langlands.Analysis.Meromorphic`):
  - weak holomorphy of scalar functions is complex differentiability;
  - identity theorems on convex and on preconnected open sets;
  - a meromorphic function vanishing on a nonempty open part of its domain
    vanishes on the whole domain (`eqOn_zero_of_open`: the set of points near
    which it vanishes is clopen);
  - restriction to a smaller open dense domain;
  - constants, sums, products, negation and finite sums;
  - `IsMeromorphicOn.eqOn_of_eqOn_open`;
  - in linear coordinates: composition with a linear equivalence, products,
    constants, finite sums and `eqOn_of_eqOn_open`.
- *Weyl parameters* (`Langlands.Global.AdelicGroupPoints`):
  - restriction of rational characters to a rational Levi subgroup is
    bijective;
  - `exists_weylParameter_linearEquiv`.
- *Regular regions* (`Langlands.GroupScheme.ParabolicRootPresentation`):
  - finiteness of the unipotent roots;
  - the regular region is open in every chart;
  - surjectivity of the real-part and restriction maps;
  - existence of a regular parameter for every threshold, from
    nondegeneracy of the Weyl-induced form and positivity of the pairing
    with the split-component cocharacter;
  - nonemptiness of the regular region in every chart.

Worker 86 added the following lemmas:

- `OpenDenseInCoordinates` with `.inter`, `.preimage` and `.iInter` (finite
  intersections of open dense sets);
- `IsMeromorphicInCoordinatesOn.openDense`;
- `isMeromorphicInCoordinatesOn_iInter_const`;
- `IsMeromorphicInCoordinatesOn.mul_const`;
- `IsMeromorphicInCoordinatesOn.sum_iInter`;
- `regularParameter_mono`;
- `eqOn_of_regular`.

## Axioms

`intertwiningCocycle_of_inputs` and `intertwiningCocycleReduction` use only
`propext`, `Classical.choice` and `Quot.sound`.

## Scope

The premises (FE), (IC), (PC) and (GI) are not proved here. Together with
proofs of them, `intertwiningCocycleReduction` yields
`IntertwiningCocycleStatement` in the same universe.
