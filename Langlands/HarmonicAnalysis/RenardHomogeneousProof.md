# Renard II.3.9: proof of the invariant-functional and comparison statements

Worker 67, Task 5524. The theorem
`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.statements` proves the
published proposition
`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.Statements` at its
full universe parameter `uG`. The target pair
`Langlands/HarmonicAnalysis/RenardHomogeneousStatements.lean/.md` and its
imports are unchanged. The proof uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
II.3.9 is on printed pp.48–50 / PDF pp.54–56; the Remark refers to
II.2.4–II.2.5, printed pp.38–42 / PDF pp.44–48.

The theorem is the conjunction of five results proved in two helper modules:

1. `invariantFunctional` and 2. `averagingStatement`, in
   `Langlands.HarmonicAnalysis.RenardHomogeneousAveragingProof`. They follow
   Renard's averaging proof. The map `p(f)(g) = ∫_H f(hg) δ_G(h)⁻¹ dμ_H(h)`
   is shown to be surjective by finite induction over double cosets `H x K`.
   The right Haar distribution `T = ofMeasure μG.inv` is shown to vanish on
   `ker p` by expanding a test into coset characteristic functions and
   grouping them by double cosets. The functional `ν` is `T` composed with a
   linear right inverse of `p`. Uniqueness and positive uniqueness come from
   the Library's Haar-distribution uniqueness
   (`Distribution.RenardHaar.measureHaarBridge`,
   `Distribution.RenardHaar.positive_real_multiple`) by cancelling the
   surjective map `p`. No Fubini theorem, quotient measure or countability
   hypothesis is used.
3. `quotientTest`, 4. `compactInduction` and 5. `pointwiseModuleSheaf`, in
   `Langlands.HarmonicAnalysis.RenardHomogeneousQuotientProof`: pullback
   along the published projection to `H\G`; the identity-on-values comparison
   with `Induction.CompactFunctions`, using a uniform compact open right
   stabilizer of each twisted function; and the pointwise action of quotient
   tests with its projector-basis sheaf.

The helper Markdown files describe each argument in detail.
