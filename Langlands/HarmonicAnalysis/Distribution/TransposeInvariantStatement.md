# Transpose invariance of conjugation-invariant distributions

`Langlands.GeneralLinearConjugationDistributionTransposeStatement.{uF}` is
the following proposition; this module only defines it, and the separate
published theorem `Langlands.generalLinearConjugationDistributionTranspose`
proves it (see [Status](#status)). For every prime `p`, every actual
`F : PadicField.{uF} p`, and every natural number `n`, put
`G = Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier`. Use the normed-field
structure `F.canonicalNormedField` and the resulting topology on `G`. Every
complex algebraic distribution `D` on `G` that is invariant under conjugation
is invariant under matrix transposition.

The field universe `uF` is arbitrary and `n + 1` covers every positive rank.
The representation of a p-adic field is the Library's actual finite extension
of the p-adic numbers. No substitute group, topology, distribution space, or
transpose map is introduced.

## Exact meaning of the imported objects

The imported `HarmonicAnalysis.Distribution G` is
`Module.Dual ℂ (SchwartzBruhat G)`: all complex linear functionals on the
actual locally constant, compactly supported complex test functions.
There is no topology or continuity hypothesis on this algebraic dual.

For a homeomorphism `e`, the Library's distribution pushforward satisfies
`(e_* D)(f) = D(f ∘ e)`. Write `c_a(g) = a * g * a⁻¹` and
`τ(g) = gᵀ`. The hypothesis `IsConjugationInvariant D` says
`(c_a)_* D = D` for every `a : G`. The conclusion
`IsTransposeInvariant (n + 1) F.Carrier D` says `τ_* D = D`.
Equivalently, the proposition concludes `D(f ∘ τ) = D(f)` for every
test function from the hypothesis `D(f ∘ c_a) = D(f)` for every `a` and
every test function. These equivalences are already proved in the imported
distribution modules.

Here `conjugationHomeomorph a` is the actual inner automorphism `c_a`.
The existing `transposeHomeomorph` is the composite of inversion with
`GeneralLinear.inverseTransposeContinuous`; its underlying matrix is
exactly `g.val.transpose`, as proved by `transposeHomeomorph_coe`.
Thus the conclusion concerns ordinary transpose, with no inverse or Weyl
conjugation in the resulting map. No Haar measure or modular factor occurs.

## Original source and proof boundary

The registered original is Bernstein and Zelevinsky,
*Representations of the group GL(n,F), where F is a non-Archimedean local
field (survey)* (1976),
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Section 1.7, printed/PDF p.7, defines exactly the algebraic distribution
space above. Section 1.17, p.10, defines its homeomorphism transport and
invariance; the dual transport gives the pushforward convention above.

Section 7.3, pp.57–58, explicitly establishes that every distribution on
`GL(r,F)` invariant under conjugation is invariant under transposition.
The present proposition restricts that result to finite p-adic extensions
and positive ranks, using the existing canonical field topology. It is the
distribution assertion used inside the source's proof of the
Gelfand–Kazhdan realization theorem.

The source proves it by applying Theorem 6.13, p.56, to the conjugation
action on `X = G` and to `σ = τ`. That theorem assumes an l-group
countable at infinity acting on an l-space, and requires:

1. The action is constructive.
2. For every `a` there is `a^σ` with `c_a ∘ σ = σ ∘ c_(a^σ)`.
3. Some natural power of `σ` is the action of a group element.
4. `σ` preserves every orbit.

For this application, the source invokes Sections 6.15–6.16, pp.56–57,
for constructiveness of the conjugation action; Remark 7.4, p.58, also
mentions a direct verification. It takes `a^σ = (aᵀ)⁻¹` for the second
condition. The imported transpose/conjugation identity and involutivity of
inverse transpose give this normalization. It uses `τ² = id` for the third
condition, and conjugacy of every invertible matrix to its transpose for
the fourth.

These conditions, the relevant l-space and countability facts, and the
general invariant-distribution argument are not hypotheses of this
statement; a proof must supply whatever it uses of them. In particular,
orbit preservation alone does not supply the asserted distribution
invariance. The existing transport lemmas prove that transpose sends a
conjugation-invariant distribution to another such distribution; they do
not identify the two distributions.

The published proof `generalLinearConjugationDistributionTranspose` does not
follow the source's route through constructiveness. It applies the published
`HarmonicAnalysis.Distribution.equivariantLocalization` along the
characteristic-polynomial coefficients to the anti-invariant difference
`D - τ_* D`. Each fibre is a closed finite union of conjugacy classes, and
there it applies the published
`HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing`. It also
uses the published theorems `matrixTransposeConjugate` (every square matrix
over a field is conjugate to its transpose) and
`matrixCharpolyFiniteConjugacy` (finitely many conjugacy classes have a given
characteristic polynomial).
[TransposeInvariantProof](TransposeInvariantProof.md) describes the
implemented Lean argument.

This module only defines the proposition. It supplies no proof of transpose
invariance, no representation character, and no representation equivalence.
The generic contragredient target `Langlands.GenericContragredientStatement`
and the Gelfand–Kazhdan realization target
`Langlands.GelfandKazhdanContragredientStatement` are separate propositions.
They are proved by the separate published theorems
`Langlands.genericContragredient` and `Langlands.gelfandKazhdanContragredient`,
not by this unit or by its proof.

## Status

The proposition is proved by the theorem
`Langlands.generalLinearConjugationDistributionTranspose.{uF}` in
`Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof`. Its type is
exactly `GeneralLinearConjugationDistributionTransposeStatement.{uF}`, with
the same field universe and no added hypothesis. The proof is artifact
`a273f153-573e-4de5-a169-47a467c37f10` version 1. Its validation passed the
Lake build and exact-target checks, an independent review approved it, and it
was published at Library commit `910a6df80701415e9aa68c646393c66ac9bc7512`.
It proves only the transpose invariance of conjugation-invariant
distributions stated here.
