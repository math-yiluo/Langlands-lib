# Proof of admissibility of irreducible product-Levi representations

Author: Worker 171.

`Langlands.CuspidalSupport.irreducibleLeviAdmissibility` proves exactly
`Langlands.CuspidalSupport.IrreducibleLeviAdmissibilityTheorem.{uF,uV} F T`
from the unchanged
[`IrreducibleLeviAdmissibilityStatement`](IrreducibleLeviAdmissibilityStatement.md).
Its only outer arguments are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
It has no additional proof-valued parameter or mathematical hypothesis.

Under exactly `T.topology`, the theorem proves admissibility of every
irreducible `ω : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`, for every natural
rank `n` and every `B : GeneralLinear.BlockShape n`. Admissibility here includes
finite-dimensional fixed vectors for every open subgroup, as well as
smoothness. The input need not have a chosen tensor presentation.

## Implemented proof

Install `T.topology` and introduce `n`, `B`, `ω` and its irreducibility proof.
Install `T.leviTopologicalGroup B`, as required by the actual normalized
induction. The following published results close the target.

1. `normalizedRefinedQuasicuspidalEmbedding.{uF,uV} F T n B ω hω` supplies
   a refinement `S`, an irreducible smooth quasicuspidal representation `σ`
   of `(B.flatten S).Levi F.Carrier`, and an injective intertwiner `j`
   from `ω.representation` into
   `T.normalizedRefinedInduced B S
     (σ.representation.comp e.symm.toMonoidHom)`,
   where `e := Geometric.flattenedLeviEquiv F.Carrier B S`.
   This is the independently proved embedding theorem, not an embedding
   hypothesis. Its proof uses published minimal refined Jacquet descent,
   finite generation of the required refined Jacquet module, an irreducible
   quotient and refined first adjointness.
2. `LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility F T
   (B.flatten S) σ hσirr hσq` proves `σ.IsAdmissible`, using exactly the
   irreducibility and quasicuspidality supplied in step 1.
3. The reverse direction of
   `Parabolic.isAdmissible_flattenedLeviTransport_iff F T B S σ.representation`
   proves admissibility of `σ.representation.comp e.symm.toMonoidHom`.
   This is the actual inverse-coordinate pullback in the embedding target.
4. `Parabolic.normalizedRefinedInductionAdmissibility F T B S` proves
   admissibility of that actual normalized refined induction.
5. `Langlands.isAdmissible_of_injective j hj` transfers admissibility to
   `ω.representation`, which is the required `ω.IsAdmissible`.
   The field `ℂ` supplies its Noetherian coefficient-ring instance.
   The transfer lemma restricts the injection to the fixed vectors of each
   open subgroup and descends finite generation from the admissible target.
   Its source and target carrier universes are independent.

The only new named declaration is the final theorem. The closing `example`
checks its specialization to carrier universe `max uF uV`.

## Normalization and topologies

All groups carry the topologies induced by the supplied `T.topology`.
The flattened equivalence `e` is the published continuous group equivalence
from the flattened product Levi to the actual refined Levi. Step 3 uses its
inverse; it does not replace the group or use an arbitrary algebraic
identification.

Steps 1 and 4 use the same `T.normalizedRefinedInduced` from
`Geometric.RefinementFunctors`. Its functions satisfy
`f(q g) = χ(π q) • τ(π q)(f g)`, where
`χ = T.refinedLeviHalfModulus B S`,
`π = Geometric.refinedLeviProjection F.Carrier B S`, and
`τ = σ.representation.comp e.symm.toMonoidHom`.
The ambient product Levi acts by right translation:
`(g • f)(x) = f(x g)`.
The embedding proof starts from normalized Jacquet modules with the inverse
half modulus and uses the published refined Frobenius map, whose covariance
has the displayed positive half modulus. The induction-admissibility proof
uses inflation through `π`, the same positive half-modulus twist and
compactness of the refined parabolic quotient. Thus these two inputs use
the identical action; this assembly introduces no normalization conversion.

## Universes and the empty product

The field and representation universes `uF` and `uV` are independent.
Both `ω` and the inducing representation `σ` have carriers in `Type uV`.
The actual induced carrier can lie in `Type (max uF uV)`.
Injective admissibility transfer allows this larger target carrier.
The final example elaborates the complete target at
`IrreducibleLeviAdmissibilityTheorem.{uF,max uF uV} F T`.

There is no positivity premise or case split in the proof. At rank zero,
positivity of the block sizes and their sum being zero force `B.length = 0`.
The actual Levi is then the product over `Fin 0`, a one-element group.
The embedding theorem includes the empty refinement; the flattened shape
is empty, the refined parabolic is the whole group, and its unipotent group
is trivial. Quasicuspidality is vacuous. Quasicuspidal admissibility,
transport, induction admissibility and injective transfer all include this
case, so the implemented uniform proof applies unchanged.

The elementary reason behind this boundary case is that a nonzero vector
of an irreducible representation of the trivial group spans an invariant
line, which must be the whole space. Its fixed spaces are therefore
finite-dimensional. This explains the empty-product extension; the Lean
proof obtains it through the uniform published inputs rather than a
separate one-dimensionality lemma. It is internal boundary content, not a
claim that BZ76 treats `GL_0`.

## Actual imports and independence audit

The five direct imports, with their roles, are:

| Module | Role |
| --- | --- |
| `CuspidalSupport.IrreducibleLeviAdmissibilityStatement` | Exact target |
| `CuspidalSupport.RefinedQuasicuspidalEmbeddingProof` | Actual normalized embedding |
| `CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` | Admissibility of the irreducible quasicuspidal inducing representation |
| `Parabolic.RefinedInductionAdmissibility` | Inverse flattened-coordinate transport and actual refined induction admissibility |
| `Smooth.Admissibility.EmbeddingProof` | Transfer through the injective intertwiner |

Each name in the table has prefix `Langlands.Representation`.
Their recursive project import closure was traversed from the actual `import`
lines against Library commit
`9076dbdeff7e1d9a1bddd23c2f62e11d180814a1`: it contains 112 project modules,
excluding this new proof module. Every imported Lean/Markdown pair in the
workspace was byte-identical to that Library. The exact target pair and all
its imports remain unchanged.

The proof dependencies have the following lower routes.

- The embedding uses `MinimalRefinedJacquetProof` for descent,
  `NaturalFirstAdjointness` for the actual refined Frobenius map, generic
  cyclicity/coatom/quotient lemmas from `QuasicuspidalEmbeddingProof`,
  compactness of the refined parabolic quotient from
  `RefinedInductionAdmissibility`, and a finite double-coset cover from
  `Induction.CompactQuotientProof`. It assumes no admissibility.
  Descent uses the published refinement-transitivity and coordinate results.
  Its statement and proof are reused, not duplicated.
- Quasicuspidal admissibility uses the blockwise Cartan decomposition,
  countable-dimension Schur's lemma, compact averaging, contraction and
  vanishing of the appropriate Jacquet coinvariants. It derives its scalar
  central action and countable dimension, and has no general irreducible-Levi
  admissibility input.
- Refined induction admissibility uses the open continuous refined Levi
  projection, admissibility of inflation and open-kernel twists,
  blockwise Iwasawa compactness, and admissibility of smooth induction from
  a subgroup with compact quotient.
- Injective transfer uses only equivariance, fixed-vector linear maps and
  Noetherian module theory.

The only `Classification` modules in this closure are `Supercuspidal` and
`SupercuspidalTwist`, which provide lower definitions and character-twist
facts. The closure contains no analytic segment classification,
special-head multisegment exhaustion, ordered strong-head existence,
quotient coverage, tempered block uniqueness, square-integrable Langlands
classification, square-integrable exhaustion or regular exhaustion.
No conclusion or proof successor of the excluded tasks
`aca8805b-054f-4d56-8045-12db7f623404`,
`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`,
`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`,
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`,
`52e97845-36bb-457d-b76f-70753334b88c`,
`1cb45da2-7007-4351-a694-594fb148b8d1`,
`cd8ab97c-0b78-4bce-97c4-d307a28159a4` or
`bf433f0a-921a-428c-b0c0-6475438125ac` is an input.

There is also no admissible-factorization or second-adjointness input,
no arbitrary irreducible-Levi admissibility proof, no finite-length
admissibility proof, and no all-smooth parabolic finite-length conclusion.
A text scan of the closure for the excluded families and
`FiniteLength`, `AdmissibleFactorization`, `IrreducibleLeviAdmissib`,
`Exhaustion`, `SquareIntegrable`, `Tempered` and `SecondAdjoint` found only
the target proposition, Mathlib finite-length theory and `HasFiniteLength`
in `Category.Basic`, the Prop-valued `CuspidalInductionLengthTheorem` in
`NormalizedCuspidalInductionStatement`, and the Prop-valued
`UnipotentExhaustionClause` in `Parabolic.GeometricPrerequisitesStatement`.
Those finite-length and unipotent-exhaustion propositions supply no proof
input or hypothesis to this theorem.

## Source correspondence and provenance

The original is I. N. Bernshtein and A. V. Zelevinskii, *Representations of
the group GL(n,F), where F is a non-Archimedean local field*, Russian
Mathematical Surveys 31:3 (1976), 1–68, literature ID
`bernstein-zelevinsky-1976-representations-gln`, PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Theorem 3.25 is on printed/PDF p.35 and its proof and Lemma 3.26 are on p.36.
These pages were reread directly for this proof. The original's first
reduction uses Proposition 3.19 and §3.13(d) to reduce to the quasicuspidal
case. That is exactly the reduction implemented here, through the published
normalized product-Levi embedding, induction admissibility and injective
transfer.

The quasicuspidal input has its own direct Cartan/Schur proof, described in
its paired Markdown; this assembly does not reimplement the source's
Harish-Chandra/Lemma 3.26 route. The normalized conventions come through the
embedding and refined induction modules, which document their correspondence
with Bernstein–Zelevinsky 1977, *Induced representations of reductive p-adic
groups I*, §1.8, printed p.444. This module is derived assembly of those
published proofs. It changes no definition or statement.
Earlier bounded searches of the Library notes, wiki, literature index and
central source listing found no applicable BZ76 erratum; no new source
correction is assumed here.

## Development verification

Terminal `lean_check` `bc7a6277-3d1d-43c6-aa8d-afe8fd6ec444` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled this module, including its
saturated-universe example, with zero errors and warnings. Declaration
inspection reports independent levels `uF,uV` and only `propext`,
`Classical.choice` and `Quot.sound`. This is a development check; independent
exact-target validation, semantic review and publication remain separate.
