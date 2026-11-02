# Affine quotients pull back along cartesian morphisms: proof

Authors: Worker 239, Worker 1224.

This module proves
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientStatement.{u}`
with the theorem
`Langlands.AlgebraicGeometry.etaleEquivalenceRelationCartesianAffineQuotient`. Recall the
statement: let `(f, g) : E ⟶ E₀` be a cartesian morphism of étale equivalence relations,
with `E.U` and `E₀.U` affine. If `E₀` has an affine quotient, then so does `E`. The proof uses
the algebraic helper `Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent`, the
published definitions of `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` and Mathlib.
It uses no other published statement as a hypothesis. It depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## The implemented proof

Write `IsCartesianHom E E₀ f g` as `hgt : g ≫ E₀.t = E.t ≫ f` and
`hpb : IsPullback g E.s E₀.s f`, and `E₀.HasAffineQuotient` as an affine `M₀` with
`q₀ : E₀.U ⟶ M₀` flat, locally of finite presentation and surjective, and
`hpb₀ : IsPullback E₀.t E₀.s q₀ q₀`.

1. Affineness. `E₀.R` is affine by `IsAffine.of_isPullback hpb₀`, and then `E.R` is affine by
   `IsAffine.of_isPullback hpb`. Every morphism between affine schemes is affine (Mathlib
   instance `isAffineHom_of_isAffine`).
2. Unit and composition. The field `refl` at `T = E.U` gives `diag : E.U ⟶ E.R` with
   `diag ≫ E.t = diag ≫ E.s = 𝟙`. The field `trans` at `T = pullback E.s E.t` gives
   `comp : pullback E.s E.t ⟶ E.R` with `comp ≫ E.t = fst ≫ E.t` and
   `comp ≫ E.s = snd ≫ E.s`.
3. The outer square. Pasting `hpb` and `hpb₀` horizontally, and rewriting with `hgt`, gives
   `IsPullback (E.t ≫ f) E.s q₀ (f ≫ q₀)`: `E.R ≅ E₀.U ×_{M₀} E.U`.
4. Rings. Mathlib's `isPushout_appTop_of_isPullback` turns this square and the pullback
   square of `E.s` and `E.t` into pushout squares of global sections. With
   `A₀ = Γ(M₀)`, `B₀ = Γ(E₀.U)`, `B = Γ(E.U)`, `C = Γ(E.R)` and
   `C₂ = Γ(pullback E.s E.t)`, the first is `C = B₀ ⊗[A₀] B` and the second is
   `C₂ = C ⊗[σ, B, τ] C`. Here `φ = q₀.appTop`, `F = f.appTop`, `τ = E.t.appTop` and
   `σ = E.s.appTop`. `φ` is faithfully flat by Mathlib's
   `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`. The global sections of `diag`
   and `comp` satisfy the unit and composition identities of step 2. Since
   `E.t ≫ f ≫ q₀ = E.s ≫ f ≫ q₀`, the image of `A₀` in `B` lies in the equalizer of `τ` and
   `σ`.
5. Descent. `isPushout_eqLocus_of_groupoid` gives a pushout square
   `A₀ → B₀, A₀ → A, B₀ → B, A → B` with `A = {b ∈ B | τ b = σ b}`.
6. The quotient. Put `M = Spec A`, `q = E.U.isoSpec.hom ≫ Spec.map (A ↪ B)` and
   `h = Spec.map (A₀ → A) ≫ M₀.isoSpec.inv`. Mathlib's `isPullback_SpecMap_of_isPushout`,
   transported along the isomorphisms `isoSpec` with `Scheme.isoSpec_hom_naturality`, gives
   `IsPullback f q q₀ h`: `E.U = E₀.U ×_{M₀} M`. Also `E.t ≫ q = E.s ≫ q`, because
   `A ↪ B` followed by `τ` or by `σ` is the same map.
7. Conclusion. The outer square of step 3 is `IsPullback (E.t ≫ f) E.s q₀ (q ≫ h)`. Since
   the right-hand square `IsPullback f q q₀ h` is a pullback, `IsPullback.of_right` makes the
   left square `IsPullback E.t E.s q q` a pullback. The morphism `q` is a base change of
   `q₀` along `h`, so it is flat, locally of finite presentation and surjective
   (`MorphismProperty.IsStableUnderBaseChange.of_isPullback`). `M` is affine. This is
   `E.HasAffineQuotient`.

## Provenance

The mathematics is descent of affine morphisms along an fpqc covering, Stacks Project
Lemma 35.37.1 (Tag 0245), in the language of presentations. It is described in the Markdown
of the statement module (sources `stacks-noetherian-approximation-2026-11-01`: `0245.html`,
`02W5.html`, `023V.html`; `stacks-etale-equivalence-relations-2026-11-01`: `03C5.html`,
`07S3.html`, `0APD.html`). The implementation does not pass through sheaves or descent data
for schemes (Tags 02W5 and 023V). Like the proof of Lemma 35.37.1 for a single flat surjective
map of affine schemes, it works with rings. It uses effective
descent for modules along the faithfully flat map `Γ(M₀) → Γ(E₀.U)`, Stacks
Proposition 35.3.9 (Tag 023N, source `stacks-descent-modules-2026-11-01`, directory SHA-256
`216c92cc547dc34f00f0eaa7354703aced00a51f02c908d58a3758395f4dfe4f`), in the coalgebra form of
the helper module. The relation's unit and composition supply the coalgebra axioms. The
step from rings back to schemes uses only Mathlib (pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`): `isPushout_appTop_of_isPullback`,
`isPullback_SpecMap_of_isPushout`, `Scheme.isoSpec_hom_naturality`, `IsPullback.paste_horiz`,
`IsPullback.of_right` and stability of `Flat`, `LocallyOfFinitePresentation` and `Surjective`
under base change.
