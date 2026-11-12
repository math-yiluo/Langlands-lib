# Unitarity of normalized induction from a cocompact closed subgroup

Author: Worker 1222. Module
`Langlands.Representation.Unitary.CompactQuotientUnitaryInductionStatement`,
namespace `Langlands.Renard.CompactRepresentation`. Statement
`CompactQuotientUnitaryInductionStatement : Prop` (universe parameters `uG`, `v`); nothing is
proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, IV.2.3 "Induction des représentations unitaires", printed pp.98–99 / PDF
pp.104–105. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

In translation: let `H` be a closed subgroup of `G` with `H \ G` compact. If `(τ, E)` is a
unitary representation of `H`, the previous section shows that `i_H^G τ` is hermitian. We
describe explicitly a `G`-invariant sesquilinear form on `i_H^G τ` inducing this hermitian
structure, and show that it is positive definite, so that `i_H^G τ` is unitary. For a pair
`(f₁, f₂)` of functions in `i_H^G E` set

`⟨f₁, f₂⟩ = ∫_{H\G} ⟨f₁(g_x), f₂(g_x)⟩_V dν_{H\G}(x)`, (IV.2.3.1)

where `g_x` represents the class `x ∈ H \ G`. For this to be well defined, the function

`g ↦ ⟨f₁(g), f₂(g)⟩_V` (IV.2.3.2)

must lie in `𝒟(G, H, δ_{H\G})` (II.3.9). Since `⟨·, ·⟩_V` is `H`-invariant and `δ_{H\G}` is
real, `⟨f₁(hg), f₂(hg)⟩_V = δ_{H\G}(h) ⟨f₁(g), f₂(g)⟩_V`; smoothness and the support condition
are clear, so (IV.2.3.2) lies in `𝒟(G, H, δ_{H\G})`. One checks at once that `⟨·, ·⟩` is a
sesquilinear form on `i_H^G E` and that it is positive. If `⟨f, f⟩ = 0`, the integral reduces
to a finite sum, which forces `f = 0`, so `⟨·, ·⟩` is a hermitian inner product.

The source has no numbered result in IV.2.3; the assertions are those of this paragraph.

## Statement

The statement quantifies over a group `G : Type uG` with `[TopologicalSpace G]`,
`[NonarchimedeanGroup G]`, `[LocallyCompactSpace G]` and `[T2Space G]`, a subgroup `H` with
`hH : IsClosed (H : Set G)`, and instances `[LocallyCompactSpace H]` and
`[CompactSpace (Induction.LeftQuotient H)]`. It sets

- `δ := Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val`, a
  smooth complex character of `H`;
- `D := renardSpace H hH` and `R := rightAction H (relativeModular H hH)`, the II.3.9 space
  `𝒟(G, H, δ_{H\G})` with right translation by `G`.

For every smooth character `χ : Induction.SmoothCharacter ℂ H` whose values are positive real
numbers and satisfy `χ(h)² = δ(h)`, every `τ : SmoothRep.{0, uG, v} ℂ H` and every
`b : InvariantPositiveForm τ.representation`, it sets `σ := twist χ τ` (the representation
`h ↦ χ(h) τ(h)`), `I := Induction.CompactFunctions H σ`, `ev f g := Induction.eval H σ f.1 g`
and `π := Induction.normalizedCompactInduced H χ τ.representation`, a representation of `G`
on `I`. It asserts the conjunction of:

1. there is a map `c : I → I → D` such that `(c f₁ f₂).val g = b.inner (ev f₁ g) (ev f₂ g)`
   for all `f₁, f₂ ∈ I` and `g ∈ G`, and for every linear functional `ν : Module.Dual ℂ D`
   that is
   - nonzero,
   - invariant: `ν (R g f) = ν f` for all `g ∈ G` and `f ∈ D`,
   - positive: `ν f` is a real number `≥ 0` whenever every value of `f` is a real number
     `≥ 0`,

   there is `B : InvariantPositiveForm π` with `B.inner f₁ f₂ = ν (c f₁ f₂)` for all
   `f₁, f₂ ∈ I`;
2. `IsUnitarizable π`.

## The objects

- `δ_{H\G}`. The source writes `δ_{H\G}` both in the induction (through IV.2.1) and in the
  space `𝒟(G, H, δ_{H\G})`. The statement uses the two published forms of it:
  `relativeModularCharacter H.subtype continuous_subtype_val` (module
  `Langlands.Representation.Hecke.CompactInductionModels`), the smooth character
  `h ↦ Δ_H(h) Δ_G(h)⁻¹` built from Mathlib's modular characters `Δ`, which are the inverses of
  Renard's `δ`; and `relativeModular H hH` (module
  `Langlands.HarmonicAnalysis.HomogeneousFunctions`), the `ℝ≥0`-valued character
  `h ↦ δ_G(h) / δ_H(h)` built from Renard's modular functions. Both are Renard's
  `δ_{H\G} = δ_G / δ_H` (II.3.9, printed p.48 / PDF p.54), and they agree pointwise as
  complex numbers: both unfold to the same quotient of Mathlib modular characters. This
  identity is not stated in this module.
- The half modulus `χ` is `δ_{H\G}^{1/2}`. The two conditions determine it, since a positive
  real number has exactly one positive square root. These are the conventions of the
  published IV.2.1 statement `CompactQuotientNormalizedInductionDualityStatement` (same
  namespace), which asserts that such a smooth character exists.
- `Induction.normalizedCompactInduced H χ τ.representation` is the published
  `compactInduced H (twist χ τ)`: right translation on the functions `f : G → E` with
  `f(h g) = χ(h) τ(h) f(g)`, invariant under right translation by some open subgroup and with
  compact support in `H \ G`. With `χ = δ_{H\G}^{1/2}` this is Renard's
  `i_H^G τ = ind_H^G(τ ⊗ δ_{H\G}^{1/2})` (IV.2.1.1). Its object is, by definition, the
  representation of the IV.2.1 functor `SmoothRep.toRep ⋙ normalizedCompactInductionFunctor H χ`
  at `τ`. Because `H \ G` is compact, compact induction equals smooth induction, as the source
  says in IV.2.1.
- `renardSpace H hH` is the published II.3.9 space: locally constant `f : G → ℂ` with
  `f(h x) = δ_{H\G}(h) f(x)` and `Supp f ⊆ H K` for a compact `K ⊆ G`. `rightAction` is right
  translation on it.
- `InvariantPositiveForm ρ` is a positive definite hermitian form invariant under `ρ`
  (module `Langlands.Representation.Unitary.Basic`, with Mathlib's convention that the form
  is conjugate-linear in the first variable). Renard's "unitary" in IV.2.2 is exactly the
  existence of such a form on the smooth representation, with no completeness or topology;
  `IsUnitarizable ρ` is `Nonempty (InvariantPositiveForm ρ)`. So `b` is the unitary structure
  `⟨·, ·⟩_E` of `τ`, and `B` is the source's form `⟨·, ·⟩` on `i_H^G τ`.
- `c f₁ f₂` is the function (IV.2.3.2). Since an element of `D` is determined by its values,
  the first conjunct says exactly that (IV.2.3.2) belongs to `𝒟(G, H, δ_{H\G})` for all
  `f₁, f₂`.
- `ν (c f₁ f₂)` is the integral (IV.2.3.1): Renard writes `⟨ν_{H\G}, f⟩` as
  `∫_{H\G} f(g) dν_{H\G}(g)`.

## Faithfulness notes

- The functional `ν_{H\G}`. The Theorem of II.3.9 (printed p.49 / PDF p.55) gives, up to a
  scalar, a unique right-invariant
  linear form `ν_{H\G}` on `𝒟(G, H, δ_{H\G})`, "which can be chosen positive". The statement
  does not fix one: it quantifies over all nonzero, positive, invariant linear forms. By the
  uniqueness in II.3.9 these are the positive multiples of `ν_{H\G}`, and a positive multiple
  of `⟨·, ·⟩` is again a positive definite invariant form. Quantifying over all of them avoids
  depending on the existence and uniqueness of II.3.9, which are not proved in the Library
  (they are the published, unproved
  `HomogeneousFunctions.Renard.InvariantFunctionalStatement`).
- Positivity. The source's definiteness argument ("the integral reduces to a finite sum")
  uses that `ν_{H\G}` is strictly positive on nonzero nonnegative functions. The statement
  assumes only `ν ≠ 0` and positivity in the weak sense (`ν f ≥ 0` for `f ≥ 0`), the sense of
  "positive" in II.3.9. Strict positivity follows from these and invariance: a nonnegative
  `f ≠ 0` is positive on an open `H`-stable set, finitely many right translates of this set
  cover the support of any element of `D`, so every nonnegative element of `D` is bounded by a
  multiple of a finite sum of translates of `f`; as `ν ≠ 0` and every element of `D` is a
  combination of nonnegative ones, `ν f > 0`. This derivation is part of the proof obligation.
- "Inducing this hermitian structure": the source refers to the hermitian structure of
  IV.2.1, the nondegenerate invariant hermitian form making `i_H^G τ` hermitian. A positive
  definite invariant form is such a form, so `B` provides it. The statement does not restate
  the IV.2.1 identification `(i_H^G τ)^h = i_H^G(τ^h)`; that is
  `CompactQuotientNormalizedInductionDualityStatement`.
- `IsUnitarizable π` is the source's conclusion "`i_H^G τ` is unitary". Given the first
  conjunct it follows from the existence of one nonzero, positive, invariant `ν`, that is,
  from the existence part of II.3.9. It is stated separately because the first conjunct alone
  would be vacuous if no such `ν` existed.
- `G` is assumed nonarchimedean, locally compact and Hausdorff. For locally compact Hausdorff
  groups this is equivalent to being totally disconnected (van Dantzig), Renard's "groupe
  t.d.". `[LocallyCompactSpace H]` is needed by `relativeModularCharacter`; it holds for every
  closed subgroup of a locally compact group, so it adds no restriction.
- Every smooth `τ` with an invariant positive definite form is allowed, with no admissibility
  or finiteness assumption, as in the source.

## Related Library results

Special cases with an explicit integral are proved: `Aubert.General.compactQuotientNormalizedInductionForm`
(module `Langlands.Representation.Aubert.General.NormalizedInductionUnitarity`) gives an
invariant positive form on normalized induction from a closed cocompact `P = M ⋉ U` when `G` is
unimodular and the modular character of `P` is the Haar modulus of conjugation on `U`; the
parabolic case `leviInductionUnitarizable_of_inputs` (module
`Langlands.Representation.Exponents.MaximalLeviReducibilityInductionInputs`) uses it. These
cover the uses of IV.2.3 for parabolic induction of reductive groups; the present statement is
the source's general case of an arbitrary closed cocompact subgroup and a non-unimodular `G`.

## Remaining obligations

The proof is a separate obligation. It needs: the covariance computation
`⟨f₁(hg), f₂(hg)⟩ = δ_{H\G}(h) ⟨f₁(g), f₂(g)⟩`, using `χ` real and `χ² = δ`, and the
agreement of the two published forms of `δ_{H\G}`; local constancy of (IV.2.3.2) from the
smoothness of `f₁, f₂`; the support condition, from a compact `K ⊆ G` with `H K = G`, which
exists because `H \ G` is compact and `G` is locally compact; sesquilinearity, hermitian
symmetry, positivity and `G`-invariance of `ν ∘ c`; definiteness from the strict positivity
of `ν` derived above; and, for `IsUnitarizable π`, the existence of a nonzero, positive,
invariant `ν`, which is the existence part of II.3.9 (`InvariantFunctionalStatement`,
unproved). None of this is asserted here.

## Provenance

Source assertions of Renard 2026 IV.2.3, for an arbitrary closed subgroup with compact
quotient and every unitary smooth representation: (IV.2.3.2) lies in `𝒟(G, H, δ_{H\G})`, the
form (IV.2.3.1) is a `G`-invariant positive definite hermitian form, and `i_H^G τ` is unitary.
Formal choices: the IV.2.1 conventions of the published
`CompactQuotientNormalizedInductionDualityStatement` (published `relativeModularCharacter`,
half modulus characterized by two conditions, published normalized compact induction); the
published II.3.9 space `renardSpace` for `𝒟(G, H, δ_{H\G})`; the published
`InvariantPositiveForm` for Renard's unitary structures; and quantification over all nonzero,
positive, invariant linear forms in place of a fixed `ν_{H\G}`.
