# Proof of Tadić's exhaustion reduction

Author: Worker 1792 (using Worker 1745's `TadicXBlockAdapters`). Module
`Langlands.Representation.Classification.TadicExhaustionReductionProof`.

`Langlands.Classification.tadicExhaustionReduction` proves exactly the published
proposition `Langlands.Classification.TadicExhaustionReduction.{uF, uV} F T` of
`Classification.TadicExhaustionReductionStatement`, for arbitrary
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` with
independent universes. It has no further hypotheses; the three hypotheses of the
implication are its premises.

The proof applies `tadicUnitaryDualExhaustion_of_ingredients` of
`Classification.TadicExhaustionAssembly`, which carries out Tadić's induction on the
rank (proof of Theorem A.10, printed pp.378–379): it proves
`⟨a(n,d)^ρ⟩ = L(a(d,n)^ρ)` for unitary `ρ` in every rank
(`tadicSocleHeadDuality`), and then factors every irreducible unitarizable
representation into Tadić building blocks by Lemma 4.8(ii). The helper modules and
their roles are described in their own Markdown files: `TadicSpehHeads` (Langlands
heads of `a(d,n)^ρ` are Speh representations), `TadicSupportIdentification`
(supports and unitary twist rigidity), `TadicSocleIndependence` (socles of one
multisegment are isomorphic), `MultisegmentConstituentRealTwistCompatibilityProof`,
`TadicRectangleCombinatorics` (`a(d,n)^ρ` is not a sum of smaller pieces) and
`TadicHeadPieceFactorization` (members of `X_m` in Langlands form, and the
contradiction with Corollary A.6(ii) and the classification).
