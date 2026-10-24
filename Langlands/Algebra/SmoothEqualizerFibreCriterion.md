# A fibrewise criterion for equalizers of smooth algebras

Authors: Worker 299 and Worker 362. Worker 299 derived the algebraic
formulation and proposed the later proof route; Worker 362 checked the
retained sources and Mathlib interfaces and implemented this statement pair.

## Statement

`Langlands.Algebra.SmoothEqualizerFibreCriterion.{u}` is a `Prop`-valued
definition in an arbitrary universe `u`. All three rings, their commutative
ring structures, their algebra structures, and both maps are quantified
inside the proposition.

Let `A`, `C₀`, and `C₁` be commutative rings in `Type u`, with `A`-algebra
structures on `C₀` and `C₁`, and let `δ₁ δ₂ : C₀ →ₐ[A] C₁`. Assume:

1. `Algebra.Smooth A C₀` and `Algebra.Smooth A C₁`.
2. `Module.FaithfullyFlat A C₀`.
3. For every prime ideal `P` of `A`, every element of
   `P.ResidueField ⊗[A] C₀` on which `id ⊗ δ₁` and `id ⊗ δ₂` agree
   belongs to the range of the canonical scalar map from `P.ResidueField`.

The conclusion is that every `c : C₀` satisfying `δ₁ c = δ₂ c` belongs to
`Set.range (algebraMap A C₀)`, equivalently, there is an `a : A` with
`algebraMap A C₀ a = c`.

The fibre maps are the actual Mathlib algebra homomorphisms
`Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δᵢ`. They send
`r ⊗ c` to `r ⊗ δᵢ c` and land in `P.ResidueField ⊗[A] C₁`.
The map whose range occurs in the fibre hypothesis is
`algebraMap P.ResidueField (P.ResidueField ⊗[A] C₀)`, sending `r` to
`r ⊗ 1`. The binder `∀ (P : Ideal A) [P.IsPrime]` covers every prime
ideal, including nonmaximal primes.

The three structural hypotheses are explicit implications. There is no
noetherian, reduced, local, domain, field, finite-dimensionality, or
finite-module assumption on the rings. Smoothness is Mathlib's existing
finite-presentation and formal-smoothness condition. The fibre hypothesis
concerns only residue fields of `A`; it does not assume the desired
conclusion for other coefficient rings. The module states the proposition
without proving it.

## Čech interpretation and provenance

This is a derived algebraic statement proposed by Worker 299. It is not
literally the statement of the Stacks Project,
[Lemma 36.32.5, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62).
That lemma says that for a proper, flat, finitely presented morphism
`f : X → S`, the hypothesis
`κ(s) = H⁰(X_s, O_{X_s})` for every point `s` implies
`f_* O_X = O_S`, universally after base change. It also gives a local
decomposition of the derived pushforward; the Lean proposition here
encodes neither that decomposition nor higher cohomology.

The intended application is the Čech form over an affine base of this
degree-zero conclusion. For a separated smooth scheme `X` over `Spec A`
with a finite affine open cover, let `V` be the disjoint union of the
covering opens. Then `V` is affine, and `V ×_X V` is affine by
separatedness. Take `C₀ = Γ(V, O_V)` and
`C₁ = Γ(V ×_X V, O)`, with `δ₁` and `δ₂` induced by the two projections.
The sheaf gluing condition identifies their equalizer with `Γ(X, O_X)`.
After base change to `κ(P)`, the equalizer of the two base-changed maps
computes `Γ(X_P, O_{X_P})`. This description does not assume that taking
the original equalizer commutes with this base change.

Both Čech algebras are smooth over `A`. In the intended proper smooth
family with nonempty fibres, `V → Spec A` is flat and surjective, so
`C₀` is faithfully flat over `A`. The residue-field hypothesis expresses
that every global function on each fibre is scalar. The conclusion then
says that every global function on `X` is scalar. Faithful flatness
supplies injectivity of the scalar map, while scalars automatically
equalize two `A`-algebra homomorphisms. Thus the requested range
conclusion gives the desired identification in this geometric application.
The Lean statement itself quantifies over arbitrary algebras satisfying
its hypotheses; it requires no chosen scheme, cover, or Čech identities.
This generality is an additional algebraic proof obligation, not a
claim that Tag 0E62 directly proves the proposition for arbitrary maps.

The motivating downstream statement is
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions`.
Stacks [Lemma 36.32.6, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L)
deduces the relative global-functions conclusion for proper flat finitely
presented families with geometrically reduced and connected fibres from
Tag 0E62 and the field case. The present algebraic criterion is intended
to support that reduction without formalizing the source's perfect-complex
argument. Its proof, and the scheme-to-algebra translation, remain
separate obligations.

## Retained sources and formalization boundary

- `stacks-global-functions-field-and-fibre-criterion-2026-10-23`,
  directory SHA256
  `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`,
  file `0E62.html`: Lemma 36.32.5 and its proof.
- `stacks-relative-global-functions-0e0l-2026-10-22`,
  directory SHA256
  `4f31e85523053c46b315dc46c77b611347154add7f98d9d89a57a748f3e85b87`,
  file `0E0L.html`: Lemma 36.32.6 and its proof.

Both retained pages were read, including their proofs; neither has
comments. No source-specific project errata note was found.
The proposed later proof uses a noetherian module argument followed by
finite-presentation approximation. This is a proof plan from Worker 299,
not a theorem assumed or proved in this module. The target remains the
full proposition over arbitrary `A`.
