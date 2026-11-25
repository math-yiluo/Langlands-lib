# Henniart's candidate existence from its global inputs over totally complex fields

This module declares the **statement**
`Langlands.Henniart.CandidateExistenceTCReductionStatement`, with universe parameters
`uK uW uP uE uQ`. It is a proposition definition, and the file contains no proof of
it. It is the published `CandidateExistenceReductionStatement`
(`Langlands.Correspondence.HenniartCandidateExistenceReductionStatement`, the assembly
unit of Henniart's global construction) with three of its five hypotheses replaced by
their totally complex forms. Its provenance is *derived*, like that of the original:
Henniart's §3 has no single statement of this form.

## 1. The statement

The proposition is an implication with five hypotheses:

1. `Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP}`: Harris (1998),
   Proposition 4.8. Unchanged.
2. `ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP}`:
   Henniart (2000), Théorème 2.4, for totally complex number fields in `Type`
   (`Langlands.Automorphic.AssociatedFactorTCStatement`). It replaces
   `AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`.
3. `ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0}`: local
   finite-level class formation with its fundamental classes, for p-adic fields in
   `Type`. Unchanged.
4. `Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uW, uP}`: the
   certified local pole comparisons of Henniart's Lemme 2.8, for totally complex
   number fields in `Type` (`Langlands.Global.Factors.PoleComparisonTCStatement`). It
   replaces `RelativeCertifiedPoleComparisonsStatement.{0, uW, uP}`.
5. `Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uK, uW, uP, uE}`: the
   composite map built from a generated positive isometry at `F_v` has all
   properties of Henniart's 3.8 at every `K ≅ F_v`, for totally complex `F` in `Type`
   (same module). It replaces `HenniartCompositeMapStatement.{0, uK, uW, uP, uE}`.

Its conclusion is the conclusion of the original,
`CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`: for every prime `p`, every p-adic
field `K` in universe `uK`, and every homomorphism `q` from the absolute Galois group
of `K` to a finite group `Q` in universe `uQ`, there is a candidate at `q`, that is, a
`ℤ`-linear equivalence `Φ : W ≃ A` from a submodule `W` of the unitary Weil lattice of
`K` containing every unitary class that factors through `q` to a submodule `A` of the
unitary supercuspidal lattice of `K`, with every property of Henniart's 3.8
(`LatticeMap.HenniartProperties`). The universe levels, including the automorphic
lattice universe `0`, are those of the original; their reasons are in
`HenniartCandidateExistenceReductionStatement.md` §2.

## 2. Relation to the original

Each totally complex hypothesis follows from the corresponding unrestricted one (the
paired Markdown of `AssociatedFactorTCStatement` and `PoleComparisonTCStatement`, §3).
So this statement implies the published `CandidateExistenceReductionStatement` at the
same universe levels: given the unrestricted inputs, restrict hypotheses 2, 4 and 5
and apply this statement. A development check outside the Library compiled that
implication. The converse is not claimed. In the program of Henniart's global
construction this statement can therefore take the place of the published reduction:
its conclusion is the same, and its inputs are needed only over totally complex
fields.

## 3. Why the restriction is harmless

The globalization of Henniart (2000) §2.7 and Théorème 3.1, which uses Harris (1998)
§4, produces a CM base field `F` and a finite Galois extension `E/F`. In the
route below the global inputs are applied only at this pair. A CM field is totally
complex (Mathlib `NumberField.IsCMField.isTotallyComplex`), and so is every finite
extension of a totally complex field (`NumberField.isTotallyComplex_of_algebra`).
Inside the published proof of the globalization step, the Théorème 2.4 hypothesis is
applied only in `exists_witnessedGenerator_realizeExact`
(`Langlands.Global.Arithmetic.HenniartWitnessedGenerator`), whose one use is in
`exists_witnessedGenerator_inducedReciprocity`
(`Langlands.Global.Arithmetic.HenniartInducedGenerator`), where
`[NumberField.IsTotallyComplex F]` is already an instance argument. So the totally
complex hypotheses suffice.

## 4. A route of proof

The route is that of `HenniartCandidateExistenceReductionStatement.md` §4, with one
change. The published `RelativeGaloisGlobalization` returns `F`, `E`, `v`, `h` and `f`
by an existential, and does not record that `F` is totally complex. So this
route needs:

- a variant of `RelativeGaloisGlobalization` whose existential also records
  `NumberField.IsTotallyComplex F` (the base field produced is CM, so this costs
  nothing);
- totally complex copies of the published lemmas that pass the Théorème 2.4
  hypothesis along: `exists_witnessedGenerator_realizeExact`,
  `exists_witnessedGenerator_inducedReciprocity`,
  `exists_weilImage_realizeExact_continuousInduce`,
  `exists_weilImage_realizeExact_generator` and `henniartGlobalization_of_inputs`
  (modules `HenniartWitnessedGenerator`, `HenniartInducedGenerator`,
  `HenniartGeneratorRealization` and `HenniartGlobalizationReduction` in
  `Langlands.Global.Arithmetic`). Each copy takes that hypothesis in its totally
  complex form, adds the instance for the field at which it is applied, and is
  otherwise unchanged; the last one proves the variant of the globalization.

With the instance for `F` in hand, steps 1–5 of the original route apply verbatim,
with hypotheses 2, 4 and 5 used at the totally complex field `F`. This module proves
nothing. The Library proves the statement as `candidateExistenceTCReduction`
(`HenniartCandidateExistenceTCReductionProof`), which imports the proof of the
exact-stabilizer form (`HenniartCandidateExistenceExactStabilizerTCReductionProof`).

## 5. Source correspondence

The source is G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
sur un corps p-adique*, Invent. Math. 139 (2000), 439–455
(`henniart-2000-simple-proof`; PDF page = printed page − 438). The correspondence is
that of the original (`HenniartCandidateExistenceReductionStatement.md` §3):

- §2.7, step 1, printed p.447 (PDF 9), and Théorème 3.1, printed p.448 (PDF 10): the
  globalization of a finite Galois extension of the local field;
- Théorème 2.5 and Lemme 2.8, printed pp.446–448 (PDF 8–10): the isometry
  `R_G(F, v) ≅ R_A(F, v)`;
- §§3.7–3.8, printed p.451 (PDF 13): the composite map and its properties.

Harris's Proposition 4.8 is M. Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210
(`harris-1998-local-langlands`), printed p.201 (PDF 25). Its fields are CM fields
(`[IsCMField E] [IsCMField E']` in `Proposition48Statement`).

## 6. Scope

- Hypotheses 1 and 3 are unchanged. The proof of hypothesis 1 from Harris's inputs is
  a separate question; one point of it is whether its
  rigidity input can be proved without archimedean clauses.
- The conclusion concerns candidates only. Independence of choices and the final
  correspondence are separate targets.
- The statement asserts nothing about number fields with a real place.
