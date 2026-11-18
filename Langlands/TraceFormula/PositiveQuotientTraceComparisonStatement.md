# Trace of `R(f)` on the positive quotient equals trace of `R(f¹)` on the norm-one quotient (statement)

Module `Langlands.TraceFormula.PositiveQuotientTraceComparisonStatement` contains one
proposition definition and no proof:

- `Langlands.TraceFormula.PositiveQuotientTraceComparisonStatement.{u}`.

The Library's `L²` space of automorphic forms for an adelic group is
`L²(A⁺ G(F) \ G(𝔸_F))`: the quotient of `G(𝔸_F)` by the rational points `G(F)` and by the
positive real points `A⁺` of a central split torus. Its operator `R(f)` is the integrated right
regular action of a compactly supported continuous function `f` on `G(𝔸_F)`. Abstract trace
formulae, on the other hand, are stated on `L²(Γ \ H)` for a discrete subgroup `Γ` of a
unimodular group `H`; here `H` is the norm-one group `G(𝔸_F)¹` and `Γ = G(F)`. This statement
compares the two operators. Integrating `f` over `A⁺` gives a function `f¹` on `G(𝔸_F)¹`.
Then `R(f)` is trace class exactly when the operator `π(f¹)` of `f¹` on
`L²(G(F) \ G(𝔸_F)¹)` is, and in that case the two traces are equal.

## Notation from the Library

The statement defines nothing new; all names below are Library declarations.

- `F : Type u` is a number field. `G : GroupScheme (Spec (CommRingCat.of F))` is a group
  scheme over `F`. Its underlying scheme is affine (`[IsAffine G.X.left]`) and locally of
  finite type over `F` (`[LocallyOfFiniteType G.X.hom]`).
- `AdelicGroupPoints F G` is `G(𝔸_F)` with its adelic topology. `normOneSubgroup F G` is the
  norm-one subgroup `G(𝔸_F)¹`, and `rationalNormOneSubgroup F G` is `G(F)`, viewed as a
  subgroup of `G(𝔸_F)¹`.
- The comparison data `T, i, hi, I, e, hc` are the parameters of the Library's positive
  quotient:
  - `T : CommGroupScheme (Spec (CommRingCat.of F))` with an isomorphism
    `e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I` onto the split torus whose
    cocharacter index type is the finite type `I : Type u` (`[Fintype I]`).
  - `i : T.toGrp ⟶ G` is a homomorphism, and `hc : IsCentral i` says it is central: every
    point of `T` maps into the centre of `G`.
  - `hi : Function.Injective (characterRestrict i)` says that restriction of rational
    characters from `G` to `T` along `i` is injective. The instance
    `[(characterRestrict i).range.FiniteIndex]` says that its image has finite index.
- `intrinsicSubgroup F T` is `A⁺`: the points of `T(𝔸_F)` at which every character of `T`
  takes values in the positive real scalar ideles (Library `scalarSubgroup`).
  `positivePointMap F G T i : intrinsicSubgroup F T →ₜ* AdelicGroupPoints F G` is the map
  `A⁺ → G(𝔸_F)` induced by `i`.
- `normalizedPositiveHaarMeasure F G T i hi I e hc` is the Haar measure on `A⁺` normalized so
  that the homeomorphism `(a, x) ↦ a x : A⁺ × G(𝔸_F)¹ → G(𝔸_F)` (`normOneDecomposition`)
  carries its product with `Measure.haar` on `G(𝔸_F)¹` to `Measure.haar` on `G(𝔸_F)`. This is
  the Library theorem `map_normalizedPositiveHaarMeasure_prod`.
- `Langlands.Analysis.integratedIsometricAction μ π hπnorm hπmeas φ hφ`
  (`Langlands/Representation/Unitary/IntegratedOperator.lean`) is defined for a homomorphism
  `π` from a group to the bounded operators on a Banach space `E`, with isometric `π(g)`
  (`hπnorm`), almost everywhere strongly measurable orbits (`hπmeas`), and a `μ`-integrable
  `φ` (`hφ`). It is the bounded operator whose value on a vector `v ∈ E` is the `E`-valued
  Bochner integral
  `∫ φ(g) • π(g) v dμ(g)` (Library `integratedIsometricAction_apply`). For each `v` the
  weighted orbit `g ↦ φ(g) • π(g) v` is integrable (Library
  `isometricActionIntegrand_integrable`), and the operator norm is at most `∫ |φ| dμ`. The
  operator is defined vector by vector. It is not a Bochner integral of the operator-valued
  map `g ↦ φ(g) π(g)`, which need not be Bochner integrable in operator norm for right
  regular representations.
- `haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f h` is `R(f)`. It is
  `integratedIsometricAction` for the bounded right regular action `ρ` of `G(𝔸_F)` on
  `L²(A⁺ G(F) \ G(𝔸_F))`. Here the `L²` space is taken for the Library's quotient measure
  `positiveRationalQuotientHaarMeasure F G T i`, and `ρ(g)` is right translation by `g`. So
  `R(f) φ = ∫ f(g) • ρ(g) φ dg` for each `φ`, an `L²`-valued Bochner integral with `dg` the
  measure `Measure.haar` on `G(𝔸_F)` (Library `haarQuotientL2IntegratedAction_apply`). The
  argument `h` is a proof that `f` is integrable.
- `NormOneRationalQuotient F G` is the coset space `G(F) \ G(𝔸_F)¹`. By definition it is
  `LeftCosetSpace (rationalNormOneSubgroup F G)`, which unfolds to the Library's
  `LeftQuotient (rationalNormOneSubgroup F G)`. `normOneRationalQuotientHaarMeasure F G` is
  its Library quotient Haar measure, written `ν¹` below.
- `Langlands.QuotientIntegration.rightTranslate Γ g` is right translation by `g` on `Γ \ H`.
  It sends the coset of `x` to the coset of `x g`.
- `IsTraceClass A` (Library, `Langlands.Analysis.OperatorIdeals`) says that for some Hilbert
  basis `b` the real parts of the diagonal entries `⟨b_k, |A| b_k⟩` of the positive left
  modulus `|A|` form a summable family. `traceIn b A` is the diagonal sum
  `∑' k, ⟨b_k, A b_k⟩` in a Hilbert basis `b`. It is a Lean `tsum`, so it is `0` when the
  diagonal is not summable. `operatorTrace A` is `traceIn b A` for one fixed Hilbert basis
  `b` of the space, chosen by `Classical.choose`.

## Statement

Fix a number field `F` in universe `u`, an affine group scheme `G` over `F` locally of finite
type, and comparison data `T, i, hi, I, e, hc` as above. Assume that `Measure.haar` on
`G(𝔸_F)¹` is right invariant (the instance `haarQuotientL2IntegratedAction` requires). Let
`f : C_c(AdelicGroupPoints F G, ℂ)` be a compactly supported continuous function, and put

`fOne(x) = ∫_{A⁺} f(positivePointMap a · x) da` for `x ∈ G(𝔸_F)¹`,

where `da` is `normalizedPositiveHaarMeasure F G T i hi I e hc`. Then:

1. `fOne` is continuous and has compact support.
2. Let `h` be a proof that `f` is integrable for `Measure.haar` on `G(𝔸_F)`, and `hOne` a
   proof that `fOne` is integrable for `Measure.haar` on `G(𝔸_F)¹`. Let
   `π : G(𝔸_F)¹ →* (L²(ν¹) →L[ℂ] L²(ν¹))` be a representation by bounded operators that
   satisfies these three conditions:
   - `hπnorm`: each `π(g)` is isometric, `‖π g φ‖ = ‖φ‖`;
   - `hπmeas`: each orbit `g ↦ π g φ` is almost everywhere strongly measurable for
     `Measure.haar`;
   - `π` acts by right translation: for all `g` and `φ`, `π g φ` agrees `ν¹`-almost
     everywhere with `q ↦ φ(rightTranslate (rationalNormOneSubgroup F G) g q)`.

   Write `π(fOne)` for `integratedIsometricAction Measure.haar π hπnorm hπmeas fOne hOne`, so
   that `π(fOne) v = ∫ fOne(n) • π(n) v dn` for each `v ∈ L²(ν¹)`. Then:
   - `R(f)` is trace class if and only if `π(fOne)` is trace class, and
   - if `R(f)` is trace class, then `operatorTrace R(f) = operatorTrace π(fOne)`.

`h` and `hOne` are proofs of propositions, so the operators do not depend on which proofs are
given. They always exist: `f` is integrable because it is continuous with compact support, and
by part 1 so is `fOne`.

### Why the trace equality is stated only for trace class operators

`operatorTrace` is the diagonal sum in one Hilbert basis of each space, chosen by
`Classical.choose`. The bases chosen for `L²(A⁺ G(F) \ G(𝔸_F))` and for
`L²(G(F) \ G(𝔸_F)¹)` are unrelated. Outside the trace class, the diagonal sum can depend on
the basis. For example, on `ℓ²` take the orthogonal sum over `k ≥ 1` of the `2 × 2` blocks
`(1/k) diag(1, -1) + (1/k²) I`. This operator is not trace class. In the standard basis its
diagonal is not summable, so the `tsum` is `0`. In the basis rotated by 45° within each block,
its diagonal is `1, 1, 1/4, 1/4, 1/9, 1/9, …`, which is summable with sum `2 ζ(2) ≠ 0`. For
other operators outside the trace class, such as the identity of an infinite-dimensional space,
the sum is `0` in every basis. So the statement makes no claim about the two traces outside the
trace class.

For a trace class operator, the diagonal is absolutely summable in every Hilbert basis and its
sum is the same in every Hilbert basis. This is the Library statement
`Langlands.Analysis.OperatorIdeals.TraceBasisIndependenceStatement`
(`Langlands/Analysis/TraceBasisStatement.lean`), proved as `traceBasisIndependence` in
`Langlands/Analysis/TraceBasisProof.lean`. So on the trace class, `operatorTrace` does not
depend on the chosen basis, and the trace equality is meaningful there. By the first
conclusion, the hypothesis "`R(f)` is trace class" can equally be read as "`π(fOne)` is trace
class".

### The representation `π`

The three conditions on `π` are those that the abstract simple trace formula of this program
puts on its representation. In the shared draft of that statement (Task 7420,
`Langlands.TraceFormula.AbstractSimpleTwistedTraceFormulaStatement`, draft revision 2), they
read: `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)`, `hπnorm`, `hπmeas` for the Haar measure on `G`,
and almost everywhere right translation on `LeftQuotient Γ`. Take `G = G(𝔸_F)¹`,
`Γ = G(F)` and `ν = ν¹`. Then the hypotheses here are literally of that form, because
`NormOneRationalQuotient F G` unfolds to `LeftQuotient (rationalNormOneSubgroup F G)`. So a
proof can apply the abstract formula to `π(fOne)` and transfer the result to `R(f)` with this
statement. This module does not import that draft.

The statement quantifies over `π`; it does not construct one. The almost-everywhere condition
fixes each `π g φ` as an element of `L²(ν¹)`, so any two such `π` are equal.

## Why it is true (for the reviewer; not part of the Lean)

The reason is that integrating over `A⁺` turns `R(f)` into a unitarily equivalent operator on
the norm-one quotient. The Lean statement records only the two consequences above; it does not
state the unitary equivalence.

1. Support and continuity. The map `(a, x) ↦ a x : A⁺ × G(𝔸_F)¹ → G(𝔸_F)` is a homeomorphism
   (Library `normOneDecomposition`). If `fOne(x) ≠ 0`, then `a x` lies in the support of `f`
   for some `a`. So `x` lies in the projection to `G(𝔸_F)¹` of the preimage of that support,
   which is compact. Continuity follows by dominated convergence: for `x` in a compact
   neighbourhood, the integrand is bounded by `sup |f|` times the indicator of a fixed compact
   subset of `A⁺`.
2. The unitary. `j = positiveQuotientMeasurableEquiv F G T i hi I e hc` maps
   `G(F) \ G(𝔸_F)¹` to `A⁺ G(F) \ G(𝔸_F)`, sending the coset of `n` to the coset of `n`. It
   is a homeomorphism and carries `ν¹` to `positiveRationalQuotientHaarMeasure` (Library
   `measurePreserving_positiveQuotient`). So `U φ = φ ∘ j` is a unitary operator from
   `L²(A⁺ G(F) \ G(𝔸_F))` onto `L²(G(F) \ G(𝔸_F)¹)`.
   - For `a ∈ A⁺`, `ρ(a)` is the identity: `positivePointMap a` is central and lies in the
     subgroup `A⁺ G(F)` that is divided out on the left.
   - For `n ∈ G(𝔸_F)¹`, `j` commutes with right translation by `n` (Library
     `positiveQuotientHomeomorph_rightTranslate`). With the almost-everywhere hypothesis on
     `π`, this gives `U ρ(n) = π(n) U` as operators.
3. The integrated operators, one vector at a time. Fix `φ` in `L²(A⁺ G(F) \ G(𝔸_F))`. The
   weighted orbit `g ↦ f(g) • ρ(g) φ` is an integrable `L²`-valued function (Library
   `haarQuotientL2ActionIntegrand_integrable`). The map `(a, n) ↦ a n` is measure preserving
   from the normalized product measure to `Measure.haar` on `G(𝔸_F)` (Library
   `measurePreserving_normOneDecomposition`). Change variables along it, then apply Fubini's
   theorem for `L²`-valued Bochner integrals on `A⁺ × G(𝔸_F)¹`, integrating over `A⁺`
   first. Since `ρ(a n) φ = ρ(n) φ`, the inner integral is
   `∫_{A⁺} f(a n) • ρ(n) φ da = fOne(n) • ρ(n) φ`. Hence
   `R(f) φ = ∫ fOne(n) • ρ(n) φ dn`. The Library's
   `integral_normOneDecomposition_fubini_symm` is the same computation for complex-valued
   integrands. The vector-valued version uses the same measure preservation, together with
   Mathlib's `integral_prod_symm`. Applying the bounded operator `U`, which commutes with
   Bochner integrals, and using step 2:
   `U R(f) φ = ∫ fOne(n) • π(n) (U φ) dn = π(fOne) (U φ)`. So `U R(f) U⁻¹ = π(fOne)`.
4. Unitary conjugation preserves the left modulus, `|U A U⁻¹| = U |A| U⁻¹`. It carries a
   Hilbert basis `b` to the Hilbert basis `U b` with the same diagonal entries for the
   conjugated operator. So it preserves the trace class, and `traceIn (U b) (U A U⁻¹) =
   traceIn b A`. On trace class operators the trace does not depend on the basis
   (`traceBasisIndependence`), so the two `operatorTrace` values, computed in the two chosen
   bases, agree.

## Source and what is derived

This is derived content; the source does not state it in this form. The source is Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`.

- Corollary 18.4.1 (§18.4, printed p. 485, PDF p. 492) is the simple trace formula (18.27),
  `∑_π m(π) tr π(f) = ∑_[γ] τ(C_γ) O_γ(f)`, for `f ∈ C_c^∞(A_G \ G(𝔸_F))`. It has two
  hypotheses: `R(f)` has cuspidal image, and every element of `G(F)` that is
  `G(𝔸_F)`-conjugate to the support of `f` is elliptic and semisimple. On the left, `π` runs
  over the isomorphism classes of cuspidal automorphic representations of `A_G \ G(𝔸_F)`.
  `m(π)` is the multiplicity of `π` in the cuspidal spectrum of `L²([G])`, and `tr π(f)` is
  the trace of `π(f)` on the space of the cuspidal representation `π`. On the right, `[γ]`
  runs over the elliptic semisimple conjugacy classes in `G(F)`. The paragraph after the
  corollary fixes a Haar measure on `A_G \ G(𝔸_F)` and uses it to define the operators `π(f)`
  and their traces.
- §2.6 (printed pp. 68–69, PDF pp. 85–86) defines the norm-one group `G(𝔸_F)¹` in (2.19) and
  the subgroup `A_G` in (2.20), both on printed p. 68. On printed p. 69 it defines the adelic
  quotient `[G] := A_G G(F) \ G(𝔸_F)` (2.21). The canonical map
  `G(F) \ G(𝔸_F)¹ → [G]` (2.22) intertwines the right actions of `G(𝔸_F)¹`. When `G` is
  reductive and `F` is a number field, it is a homeomorphism (Lemma 2.6.2). So for such `G` one
  can work on `G(F) \ G(𝔸_F)¹` instead of `[G]`, as the source remarks.

The Library works with functions `f` on `G(𝔸_F)` and with the quotient
`L²(A⁺ G(F) \ G(𝔸_F))`, where `A⁺` plays the role of `A_G`. The present statement is the
derived step from this setting to the norm-one realization (2.22), at the level of operators.
Integrating `f` over `A⁺` is the passage from functions on `G(𝔸_F)` to functions on
`A⁺ \ G(𝔸_F)`, which `normOneDecomposition` identifies with `G(𝔸_F)¹`. The statement then
compares the whole operators `R(f)` on `L²(A⁺ G(F) \ G(𝔸_F))` and `π(fOne)` on
`L²(G(F) \ G(𝔸_F)¹)`. It does not concern the decomposition of `L²` into cuspidal
representations or the individual traces `tr π(f)` of (18.27). The measures are the Library's
normalizations, not those of the source.

The present statement uses compactly supported continuous `f`, not smooth `f`. It involves no
cuspidal-image, ellipticity or semisimplicity hypothesis and no orbital integrals.

## Relation to other tasks

- Task 7340 is the parent task (simple trace formula, twisted form, and local cyclic base
  change for `GL_n`).
- Task 7585 (`Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaStatement`, shared draft)
  states the simple trace formula for `GL_n` in terms of the Library's `R(f)` and this `fOne`.
  Its conclusion includes that `R(f)` is trace class, and it expresses the trace of `R(f)` by
  orbital integrals of `fOne`. A proof can use the abstract formula (Task 7420) for `π(fOne)`
  and transfer the trace class property and the trace with this statement. The trace equality
  is only needed once `R(f)` is known to be trace class.
- This module imports neither.

## What this module does not claim

- It does not claim that any `R(f)` or `π(fOne)` is trace class.
- It does not claim that the traces agree when `R(f)` is not trace class.
- It does not construct `π` or show that one exists; it quantifies over all `π` with the
  stated properties.
- It does not state the unitary equivalence itself, only its consequences for the trace class
  and the trace.
- It concerns only the Library's measures: `Measure.haar` on `G(𝔸_F)` and `G(𝔸_F)¹`, the
  normalized Haar measure on `A⁺`, and the Library's quotient measures. It computes no trace.
