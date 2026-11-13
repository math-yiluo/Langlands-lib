# Renard VII.3.5 (i): reduction of the composition formula to geometric inputs

Author: Worker 48. Module
`Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.

This is a conditional reduction. It proves the published
`PQIntertwiningCompositionStatement` (module
`Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements`, unchanged) from four
propositions defined here. These four are not proved in this module, so the published statement
is still not proved unconditionally.

The module contains:

- two topological lemmas, `continuous_of_forall_mul_openSubgroup` and
  `exists_isCompact_isClopen_superset`;
- an unconditional uniqueness theorem, `pqIntertwiner_eq_of_eval_one`;
- four `Prop`-valued definitions, the inputs:
  `PQBoundaryVanishingCompactSupportStatement`, `PQCompositionProductStatement`,
  `PQCompositionHaarStatement` and `PQCompositionRegularityStatement`;
- an abstract computation, `eval_one_comp_eq_of_integral_formulas`;
- the reduction theorem `pqIntertwiningComposition_of_reductions`, and the definition
  `pqIntertwiningCompositionOfReductions`, which has the same implication as its type. This
  definition is the declaration recorded for this unit.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The Proposition of VII.3.5 is
on printed p.237 / PDF p.243. The regularity part of its proof is on printed pp.237–238 / PDF
pp.243–244. The operator identity in (i) is proved on printed p.239 / PDF p.245, in the
paragraph "Nous allons maintenant démontrer les égalités entre opérateurs d'entrelacement",
which does three things:

1. It translates `d(P₁, P₃) = d(P₁, P₂) + d(P₂, P₃)` into
   `N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)`.
2. It characterizes `F̃^{<1̄}_{P₁P₃}(E)` as the `f ∈ i_{P₁}^G(E)` with
   `Supp f ∩ (N̄₁ ∩ N₃)` compact, because `N̄₁ ∩ N₃ → P₁\P₁P₃` is a homeomorphism.
3. For `f ∈ F̃^{<1̄}_{P₁P₃}(E)` and `u ∈ N̄₂ ∩ N₃`, it shows that `r(u)f ∈ F̃^{<1̄}_{P₁P₂}(E)` and
   `J_{P₂|P₁}(f)(u) = ∫_{N̄₁∩N₂} f(vu) dv`, so that
   `J_{P₂|P₁}(f) ∈ F̃^{<1̄}_{P₂P₃}(E)`. It then computes
   `J_{P₃|P₂} J_{P₂|P₁}(f)(1) = ∫_{N̄₂∩N₃} ∫_{N̄₁∩N₂} f(vu) dv du = ∫_{N̄₁∩N₃} f = J_{P₃|P₁}(f)(1)`
   and concludes with the uniqueness in VII.3.4.

Throughout, `V₁₂ = N̄₁(F) ∩ N₂(F)`, `V₂₃ = N̄₂(F) ∩ N₃(F)` and `V₁₃ = N̄₁(F) ∩ N₃(F)` are the
subgroups of `G(F)` used in the published statement.

## Topological lemmas

- `continuous_of_forall_mul_openSubgroup`: let `Γ` be a topological group, `K` an open subgroup,
  and `φ : Γ → X` a function with `φ(xk) = φ(x)` for all `k ∈ K`. Then `φ` is continuous.
  Indeed `φ` is constant on the neighbourhood `xK` of each `x`.
- `exists_isCompact_isClopen_superset`: in a locally compact nonarchimedean group, every compact
  `S` lies in a compact clopen set. The set is `S U₀`, where `U₀` is a compact open subgroup
  (Library `Jacquet.exists_isCompact_openSubgroup_subset`). It is open as a union of translates
  of `U₀`. It is compact as the product of two compact sets. It is closed because for
  `x ∉ S U₀` the whole neighbourhood `x U₀` misses `S U₀`.

## The uniqueness theorem `pqIntertwiner_eq_of_eval_one`

This is the uniqueness half of Renard VII.3.4, proved here without the integral formula. Take
parabolics `P = MN` and `Q = MU` with Levi `M`, a split component `a`, a `PQ`-regular smooth `σ`,
and intertwining operators `J, J' : i_P^G(σ) → i_Q^G(σ)` with `J(f)(1) = J'(f)(1)` for every
`f ∈ F̃^{<1̄}_{PQ}(σ)` (`boundaryVanishingSubfunctor … (identityParabolicDoubleCoset p q)`).
Then `J = J'`.

Proof, in Lean: Frobenius reciprocity (`leviFrobeniusReciprocity`) gives a linear equivalence
`F` from intertwining operators `i_P^G(σ) → i_Q^G(σ)` to intertwining maps
`r_Q^G i_P^G(σ) → σ`. It satisfies `F(J)([f]) = J(f)(1)`. Let `T` be the image of
`F̃^{<1̄}_{PQ}(σ)` in the Jacquet module (`boundarySupportImage`). By `PQ`-regularity,
`existsUnique_intertwining_extension` (module `PQIntertwiningOperatorProof`) says that an
intertwining map out of `r_Q^G i_P^G(σ)` is determined by its restriction to `T`. The
restrictions of `F(J)` and `F(J')` to `T` agree, because every element of `T` is a class `[f]`
with `f ∈ F̃^{<1̄}_{PQ}(σ)`. Hence `F(J) = F(J')`, and injectivity of `F` gives `J = J'`.

## The four input propositions

The binders and hypotheses are copied from the published statements: from
`PQIntegralIntertwiningOperatorStatement` for the first proposition (one pair `P`, `Q` and an
opposite `P̄`), and from `PQIntertwiningCompositionStatement` for the other three, up to and
including `d(P₁, P₂) = 1`. Only the conclusions are new. Some binders are unused in some
conclusions but are kept with the published names, so the definitions switch off
`linter.unusedVariables`.

### `PQBoundaryVanishingCompactSupportStatement`

The data are a nonarchimedean local field `k`, a connected reductive `G` with the canonical
topology on `G(F)` (locally compact, nonarchimedean), represented parabolics `P = MN` and
`Q = MU` with the same embedded Levi (`l ≫ p = lQ ≫ q`), and a represented parabolic
`P̄ = MN̄` opposite to `P` (`lb ≫ pb = l ≫ p`, `P(F) ∩ P̄(F) = M(F)`). Let
`V = N̄(F) ∩ U(F)`. The statement: for every smooth `σ` of `M(F)` and every
`f ∈ i_P^G(σ)`, `f ∈ F̃^{<1̄}_{PQ}(σ)` if and only if there is a compact `K ⊆ V` such that
`f(x) = 0` for all `x ∈ V \ K`.

This is item 2 of the Source section for a general pair `(P, Q)`. Renard writes "`Supp f ∩ V` is
compact". Because `f` is locally constant, that is the same as vanishing on `V` outside some
compact set. Here `F̃^{<1̄}_{PQ}(σ)` is the published `boundaryVanishingSubfunctor`: the
functions vanishing on `closure(PQ) \ PQ`.

### `PQCompositionProductStatement`

The data and hypotheses are those of `PQIntertwiningCompositionStatement` up to and including
`d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`. The conclusion is a homeomorphism
`e : V₁₂ × V₂₃ ≃ₜ V₁₃` with `e(w, u) = w u` in `G(F)`.

This is item 1 of the Source section (`N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)`). Renard states only the
equality of sets. The bijection and the homeomorphism are what the change of variables in
item 3 uses.

### `PQCompositionHaarStatement`

Clause 1 of `PQIntertwiningCompositionStatement`, copied word for word as a proposition of its
own. For all Haar measures `haar₁₂` on `V₁₂` and `haar₂₃` on `V₂₃` there is a Haar measure
`haar₁₃` on `V₁₃` with
`∫_{V₁₃} φ dhaar₁₃ = ∫_{V₂₃} ∫_{V₁₂} φ(wu) dhaar₁₂(w) dhaar₂₃(u)` for every continuous
compactly supported `φ : G(F) → ℂ`.

### `PQCompositionRegularityStatement`

The regularity part of clause 2 of `PQIntertwiningCompositionStatement`, as a proposition of its
own. With the same data and hypotheses, every `P₁P₃`-regular smooth `σ` of `M(F)` is
`P₂P₃`-regular and `P₁P₂`-regular (`IsPQRegular`). This is the first assertion of
VII.3.5 (i), proved by Renard on printed pp.237–238.

## The abstract computation `eval_one_comp_eq_of_integral_formulas`

The setting is a locally compact nonarchimedean group `Γ` with the following data:

- complex representations `ρ₁, ρ₂, ρ₃` of `Γ`, with `ρ₁` smooth;
- maps `Eᵢ : Wᵢ → Γ → S` into a complex vector space `S`, where `E₁` and `E₂` turn the action
  into right translation: `Eᵢ(ρᵢ(g) f)(x) = Eᵢ(f)(xg)`;
- subgroups `V₁₂, V₂₃, V₁₃` with measures `haar₁₂, haar₂₃, haar₁₃`;
- sets `F₁₂, F₁₃ ⊆ W₁` and `F₂₃ ⊆ W₂`.

The hypotheses are:

- `F₁₂` and `F₂₃` contain every vector whose evaluation on `V₁₂`, respectively `V₂₃`, vanishes
  outside a compact set;
- every `f ∈ F₁₃` has evaluation on `V₁₃` vanishing outside a compact set;
- a homeomorphism `e : V₁₂ × V₂₃ ≃ V₁₃` with `e(w, u) = wu`;
- the compatibility of the three measures, as in `PQCompositionHaarStatement`;
- intertwining maps `J₁₂ : ρ₁ → ρ₂`, `J₂₃ : ρ₂ → ρ₃` and `J₁₃ : ρ₁ → ρ₃` with
  `ℓ(E₂(J₁₂ f)(1)) = ∫_{V₁₂} ℓ(E₁ f) dhaar₁₂` for `f ∈ F₁₂` and every linear form `ℓ` on `S`,
  and likewise for `J₂₃` on `F₂₃` and `J₁₃` on `F₁₃`.

The conclusion: `E₃(J₂₃(J₁₂ f))(1) = E₃(J₁₃ f)(1)` for every `f ∈ F₁₃`.

Proof, following item 3 of the Source section. Fix `f ∈ F₁₃`, vanishing on `V₁₃` outside a
compact `K`. Then `e⁻¹(K)` is compact.

- For `u ∈ V₂₃`, `E₁(ρ₁(u) f)(w) = E₁(f)(wu)` vanishes for `w` outside the compact projection
  of `e⁻¹(K)` to `V₁₂`. So `ρ₁(u) f ∈ F₁₂`.
- Since `J₁₂` is an intertwining map, `E₂(J₁₂ f)(u) = E₂(J₁₂(ρ₁(u) f))(1)`. So
  `ℓ(E₂(J₁₂ f)(u)) = ∫_{V₁₂} ℓ(E₁(f)(wu)) dhaar₁₂(w)`.
- For `u` outside the compact projection of `e⁻¹(K)` to `V₂₃`, the integrand vanishes
  identically. Linear forms separate points of `S` (Mathlib
  `Module.forall_dual_apply_eq_zero_iff`), so `E₂(J₁₂ f)(u) = 0`. Hence `J₁₂ f ∈ F₂₃`.
- Fix `ℓ`. The vector `f` is fixed by an open subgroup, so `x ↦ ℓ(E₁(f)(x))` is right-invariant
  under that subgroup and is continuous by `continuous_of_forall_mul_openSubgroup`. Let `C` be a
  compact clopen set containing the image of `K` in `Γ`
  (`exists_isCompact_isClopen_superset`). Then `φ = 1_C · ℓ(E₁ f)` is continuous with compact
  support and agrees with `ℓ(E₁ f)` on `V₁₃`.
- Chaining the formula for `J₂₃` at `J₁₂ f`, the formula above, compatibility for `φ`, and the
  formula for `J₁₃` gives `ℓ(E₃(J₂₃ J₁₂ f)(1)) = ℓ(E₃(J₁₃ f)(1))`. This holds for every `ℓ`, so
  the two vectors are equal.

## The reduction `pqIntertwiningComposition_of_reductions`

Hypotheses: `PQBoundaryVanishingCompactSupportStatement.{u, v}`,
`PQCompositionProductStatement.{u}`, `PQCompositionHaarStatement.{u}` and
`PQCompositionRegularityStatement.{u, v}`. Conclusion: exactly the published
`PQIntertwiningCompositionStatement.{u, v}`.

Proof. After the common binders are introduced:

- Clause 1 is `PQCompositionHaarStatement` applied to the same data.
- The two regularity conclusions of clause 2 are `PQCompositionRegularityStatement`.
- For the operator identity, take compatible Haar measures and operators `J₁₂, J₂₃, J₁₃`
  satisfying `IsIntegralIntertwiner`. The input `PQCompositionProductStatement` gives `e`.
  `PQBoundaryVanishingCompactSupportStatement` is applied three times, with the following
  arguments:
  - `(P₁, P₃, P̄₁)`, with `l₁ ≫ p₁ = l₃ ≫ p₃`;
  - `(P₁, P₂, P̄₁)`;
  - `(P₂, P₃, P̄₂)`, with `l₂ ≫ p₂ = l₃ ≫ p₃`, `lb₂ ≫ pb₂ = l₂ ≫ p₂` and
    `P₂(F) ∩ P̄₂(F) = M(F)`, rewritten from the hypotheses through `l₂ ≫ p₂ = l₁ ≫ p₁`.
- These are the support characterizations needed by `eval_one_comp_eq_of_integral_formulas`. That
  lemma is applied with `Γ = G(F)`, `ρᵢ` the representations of `i_{Pᵢ}^G(σ)`, `Eᵢ` the
  evaluation `Induction.eval`, `S = σ`, and `F₁₂`, `F₂₃`, `F₁₃` the sets
  `F̃^{<1̄}_{P₁P₂}(σ)`, `F̃^{<1̄}_{P₂P₃}(σ)`, `F̃^{<1̄}_{P₁P₃}(σ)`. It gives
  `(J₂₃ ∘ J₁₂)(f)(1) = J₁₃(f)(1)` for all `f ∈ F̃^{<1̄}_{P₁P₃}(σ)`.
- `pqIntertwiner_eq_of_eval_one`, for the `P₁P₃`-regular `σ`, then gives `J₂₃ ∘ J₁₂ = J₁₃`.

Only the equality half of `IsIntegralIntertwiner` is used: the integrability half is not needed.

## The definition `pqIntertwiningCompositionOfReductions`

`def pqIntertwiningCompositionOfReductions :
PQBoundaryVanishingCompactSupportStatement.{u, v} → PQCompositionProductStatement.{u} →
PQCompositionHaarStatement.{u} → PQCompositionRegularityStatement.{u, v} →
PQIntertwiningCompositionStatement.{u, v} := pqIntertwiningComposition_of_reductions`.

It adds nothing to the theorem. It records the reduction as a declaration whose type is the
implication, the Library's pattern for conditional reductions (for example
`Langlands.Aubert.General.RationalPointFamily.rationalSupportCategoryDecompositionOfWholeStatement`).
The `linter.defProp` warning is switched off for it alone.

## Provenance

Derived. `PQCompositionHaarStatement` is clause 1 of the published statement.
`PQCompositionRegularityStatement` is part of clause 2. The other two inputs are statements that
Renard asserts inside the proof on printed p.239 / PDF p.245. The product statement is made
explicit as a homeomorphism `V₁₂ × V₂₃ ≃ₜ V₁₃`. The lemmas and the reduction implement Renard's
argument on that page, with uniqueness taken from Frobenius reciprocity and
`existsUnique_intertwining_extension` rather than from the integral form of VII.3.4.

## Dependencies

Imports `Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements` (unchanged),
`Langlands.Representation.Intertwining.PQIntertwiningOperatorProof` and
`Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract`. It uses no `sorry` and no new
axiom.
