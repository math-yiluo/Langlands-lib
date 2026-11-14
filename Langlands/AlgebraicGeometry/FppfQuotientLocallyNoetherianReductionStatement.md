# Reduction of the fppf quotient on locally noetherian tests to effective quotients by flat proper equivalence relations

Authors: Worker 22.

Worker 22 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). The proposition reduces the
published `FppfQuotientLocallyNoetherianStatement` (the target of proof Task
6193, `3b764af9-5a6e-4596-86a0-8a3e0529d073`) to the published
`FlatProperEquivalenceRelationQuotientStatement` (the target of proof Task
6004, `150325ad-31d8-4abe-80a5-c18a5bda8474`). The context of Task 6193
proposes exactly this implication as a separate step.

No proof is asserted here. The module only states the implication.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`):

```lean
FlatProperEquivalenceRelationQuotientStatement.{u} →
  FppfQuotientLocallyNoetherianStatement.{u}
```

Both propositions are published Library statements in the namespace
`Langlands.AlgebraicGeometry`, imported from their modules and used at the same
universe `u`.

1. The hypothesis
   `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`
   ("(c)") is about schemes. Let `A` be a noetherian ring, `p : Z ⟶ Spec A`
   H-quasi-projective (`IsHQuasiProjective p`), and `s t : R ⟶ Z` with
   `s ≫ p = t ≫ p`. Assume that `pullback.lift s t _ : R ⟶ Z ×_A Z` is a
   monomorphism, that for every scheme `T` the relation "`x` and `y` are
   `φ ≫ s` and `φ ≫ t` for some `φ : T ⟶ R`" on `T ⟶ Z` is an equivalence
   relation, and that `s` is flat and proper. Then there are an
   H-quasi-projective `q : Q ⟶ Spec A` and `π : Z ⟶ Q` with `π ≫ q = p`,
   `π` flat, surjective, proper and locally of finite presentation, and
   `IsPullback s t π π`, that is, `R = Z ×_Q Z`.
2. The conclusion
   `Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianStatement`
   ("(c'')") is about fppf sheaves on `Over (Spec A)`. Let `G` be an fppf sheaf,
   `Z` H-quasi-projective and `ζ : Z → G` fppf-locally surjective. Let
   `s t : R ⟶ Z` in `Over (Spec A)` satisfy `ζ ∘ s = ζ ∘ t`, assume that on
   every test `T` with `T.left` locally noetherian any two `T`-points of `Z`
   with the same image in `G` are `r ≫ s` and `r ≫ t` for a unique
   `r : T ⟶ R`, and assume that `s.left` is flat and proper. Then there are an
   H-quasi-projective `Q`, a flat, surjective, proper, locally finitely
   presented `π : Z ⟶ Q` and a map `e : Q → G` with `e ∘ π = ζ`, such that `e`
   is bijective on every test `T` with `T.left` locally noetherian.

The Markdown files of the two statements explain every hypothesis and
conclusion in detail.

## Source and provenance

The provenance is "derived". The implication is extracted from the proof of
Lemma 4.9 of S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`, p.30, proof pp.30–31, with
Exercise 4.10, p.31). There Kleiman applies the quotient theorem of
Altman–Kleiman [AK80, Thm. (2.9)] to the relation `R = Z ×_P Z` and then
identifies the sheaf `P` with the quotient. The quotient theorem is hypothesis
(c) here; the identification is what remains to be proved. Kleiman does not
state this implication separately.

## Intended proof

The section "Derivation of the Lean statement" of the Markdown of
`FppfQuotientLocallyNoetherianStatement` explains the argument in six steps.
Step 3 there applies (c), which here is the hypothesis. The other steps are
what a proof of the present implication has to formalize:

- **Step 1.** `Z` is of finite type over the noetherian ring `A`, and `R` is of finite
   type over `Z` because `s` is proper. The fibre products used below are
   locally of finite type over `R` or over a locally noetherian test, so they
   are locally noetherian tests.
- **Step 2.** Testing the unique-lifting hypothesis of (c'') on `R ×_{Z ×_A Z} R`, `Z`,
   `R` and `R ×_{t,Z,s} R` shows that `(s, t)` is a monomorphism and that the
   relation is reflexive, symmetric and transitive on `T`-points for every
   scheme `T`. These are the hypotheses of (c).
- **Step 4.** The map `e` is obtained by fppf descent along the covering
   `T ×_Q Z ⟶ T`, using `R = Z ×_Q Z` and `ζ ∘ s = ζ ∘ t`. Then `e ∘ π = ζ`.
- **Step 5.** On a locally noetherian test `T`, the members of fppf coverings of `T` and
   their fibre products are locally noetherian. With the unique-lifting
   hypothesis and the fact that the functor of points of `Q` is an fppf sheaf
   (Mathlib's `fppfTopology.Subcanonical`), this gives injectivity and
   surjectivity of `e` at `T`.

## Use

Worker 22's published reduction
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionStatement`
takes (c'') as a hypothesis. Together with a proof of the present implication,
a proof of (c) (Task 6004) then supplies that hypothesis.
