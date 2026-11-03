# Unipotence from the absence of zero Lie weights for split torus actions

Module `Langlands.GroupScheme.Rational.TorusUnipotenceProof`, namespace
`Langlands.GroupScheme.RelativeRoot`.

## Statement proved

`torusActionUnipotence : TorusActionUnipotenceStatement.{u}`. This proves the Library statement
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement` from
`Langlands.GroupScheme.Rational.TorusUnipotenceStatement`. Let `k` be a field and `H` a group
scheme over `Spec k` that is smooth, affine and has connected underlying space. Let `S` be a split
torus over `k` and `b : AutomorphicAction S.toGrp H` an action of `S` on `H` by group
automorphisms. If the zero Lie eigenspace `actionWeightSpace b 0` is `⊥`, then `H` is unipotent
(`IsUnipotent H`).

## Proof

Introduce the data and install the smoothness, affineness and connectedness hypotheses as
instances. Then apply `TorusUnipotence.isUnipotent_of_actionWeightSpace_zero_eq_bot` from
`Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGlue`.

That theorem is the end of a chain of helper modules in
`Langlands/GroupScheme/Rational/TorusUnipotence/`, each with its own Markdown:

1. `CotangentBasis`, `Truncation`, `TruncatedSection`: formal coordinates at the identity of a
   formally smooth augmented algebra, chosen homogeneous for a grading.
2. `BigCellStatement`, `BigCell`: for a `ℤ`-graded formally smooth Noetherian domain whose
   degree-zero augmentation elements lie in `I²`, the big-cell map `A → A/J⁻ ⊗ A/J⁺` is
   injective. This uses the Krull intersection theorem.
3. `Rigidity`, `Regrading`: big-cell injectivity gives top-weight rigidity for the grading by a
   generic cocharacter.
4. `TopWeight`, `MatrixCoefficients`: rigidity of a graded Hopf algebra gives fixed vectors of
   all matrix corepresentations, hence unipotence.
5. `CoordinateGrading`: the character grading of the coordinate algebra is compatible with the
   unit, counit and comultiplication.
6. `CoordinateGlue`: the absence of a zero Lie weight implies, through the Library's
   `CoordinateWeights.cotangentLieSupport`, that the zero character is absent from the
   augmentation cotangent space. Combined with the steps above, this gives unipotence.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., the general observation in the proof of
Proposition 2.3.11 (p. 82). The Lean route differs from CGP's, which uses a maximal torus of the
semidirect product; see `CoordinateGlue.md`.
