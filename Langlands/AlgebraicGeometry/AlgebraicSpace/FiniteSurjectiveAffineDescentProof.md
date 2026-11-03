# Finite-surjective descent of affineness for algebraic spaces (proof)

Author: Worker 239. The proof is an assembly of published theorems; their
authors are named in their own Markdown files.

The theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.finiteSurjectiveAffineDescent`
proves `AlgebraicSpace.FiniteSurjectiveAffineDescentStatement.{u}`, and its type
is exactly that statement:

```lean
∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
  IsFinite (hom f) → IsSurjective (hom f) →
    IsRepresentedByAffineScheme X → IsRepresentedByAffineScheme Y
```

This is Stacks Project Lemma 70.15.1 (Tag 07VS) for the Library's algebraic
spaces, for every base scheme and in an arbitrary universe `u`. The statement
module and its imports are unchanged. The module adds no helper modules and no
axioms. It uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Inputs

The proof imports the following published theorems. Each proves the published
statement named after it, with exactly that type.

| Short name | Theorem | Statement |
| --- | --- | --- |
| T | `etaleEquivalenceRelationAffineDescentTransfer` | `EtaleEquivalenceRelationAffineDescentTransferStatement` |
| A | `etaleEquivalenceRelationAffineRelation` | `EtaleEquivalenceRelationAffineRelationStatement` |
| Key | `etaleEquivalenceRelationComodulesAcyclic` | `EtaleEquivalenceRelationComodulesAcyclicStatement` |
| Serre | `etaleEquivalenceRelationSerreCriterion` | `EtaleEquivalenceRelationSerreCriterionStatement` |
| FL | `etaleEquivalenceRelationNoetherianFirstLevel` | `EtaleEquivalenceRelationNoetherianFirstLevelStatement` |
| NL | `etaleEquivalenceRelationNoetherianCoverLevel` | `EtaleEquivalenceRelationNoetherianCoverLevelStatement` |
| DS | `etaleEquivalenceRelationCartesianAffineQuotient` | `EtaleEquivalenceRelationCartesianAffineQuotientStatement` |

All live in the namespace `Langlands.AlgebraicGeometry`, in the modules
`Langlands.AlgebraicGeometry.<Statement name with Statement replaced by Proof>`.
Throughout, `E` is an étale equivalence relation (`EtaleEquivalenceRelation`,
absolute, over `Spec ℤ`) with scheme of objects `E.U`, scheme of arrows `E.R`
and target and source maps `E.t`, `E.s`.

## Proof

The module proves three theorems.

1. `noetherianEtaleEquivalenceRelationAffineDescent :
   NoetherianEtaleEquivalenceRelationAffineDescentStatement.{u}` (Tag 07VP
   for presentations). Let `E` have `E.U` affine and Noetherian and a finite
   surjective cartesian cover with an affine quotient. A gives `E.R` affine and
   `prod.lift E.t E.s` a closed immersion. Key then gives
   `E.ComodulesAcyclic`, and Serre gives `E.HasAffineQuotient`.
2. `etaleEquivalenceRelationNoetherianApproximation :
   EtaleEquivalenceRelationNoetherianApproximationStatement.{u}` (absolute
   Noetherian approximation for presentations). Assume the Noetherian case
   `hN`, and let `E` have `E.U` affine and such a cover. A gives that
   `prod.lift E.t E.s` is a closed immersion. FL gives a cartesian morphism
   `E ⟶ E₀` with `E₀.U` affine and Noetherian and `E₀.R` affine. NL gives a
   cartesian morphism `E ⟶ E₁` with `E₁.U` affine and Noetherian, where `E₁`
   again has a finite surjective cartesian cover with an affine quotient. Then
   `hN` gives `E₁.HasAffineQuotient`, and DS pulls the affine quotient back
   along `E ⟶ E₁`, which gives `E.HasAffineQuotient`.
3. `finiteSurjectiveAffineDescent :
   AlgebraicSpace.FiniteSurjectiveAffineDescentStatement.{u}` is T applied to
   theorem 2 applied to theorem 1.

## Provenance

The route is the proof of Stacks Lemma 70.15.1 (Tag 07VS), rewritten for
presentations by étale equivalence relations on affine schemes. Stacks reduces
the lemma to the Noetherian case, Lemma 69.17.3 (Tag 07VP), by absolute
Noetherian approximation (Proposition 70.8.1, Tag 07SU) and Lemma 70.5.10
(Tag 07SQ). The proof of the Noetherian case first shows `H^1(X, F) = 0` for
every quasi-coherent `O_X`-module `F`, and then concludes affineness by the
cohomological affineness criterion of Serre for algebraic spaces
(Proposition 69.16.7, Tag 07V6). T translates between algebraic spaces and
presentations. FL, NL and DS are the approximation steps, and A, Key and Serre
are the Noetherian case; Serre is the presentation form of Proposition 69.16.7.
The Markdown files of the seven statements explain each derivation from the
sources. The sources are registered as
`stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
`10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`, page
`07VQ.html` with Lemma 70.15.1 and its proof),
`stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
`6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`, page
`07VP.html` with Lemma 69.17.3 and its proof),
`stacks-noetherian-approximation-2026-11-01` (directory SHA-256
`a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`, pages
`07SU.html` and `07SQ.html`) and
`stacks-serre-criterion-algebraic-spaces-2026-11-01` (directory SHA-256
`87667c307924301da4b8d890a4cd77f1dbee3773a5130a698624e661014c8e5e`, page
`07V6.html` with Proposition 69.16.7, and page `07UX.html` with Situation
69.16.1, which states its hypotheses).
