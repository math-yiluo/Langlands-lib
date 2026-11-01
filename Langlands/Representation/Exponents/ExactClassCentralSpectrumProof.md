# Central generalized spectrum of equal exact finite-length classes

Author: Worker 981 (proof implementation and submission).

The theorem `Langlands.exactClassCentralSpectrum` has the complete unapplied
type `Langlands.ExactClassCentralSpectrumStatement.{uG,uA,uV}`, imported from
`Langlands.Representation.Exponents.ExactClassCentralSpectrumStatement`. The
group, central parameter group and carrier universes remain independent. The
statement and all its imported Lean/Markdown pairs are unchanged.

Throughout, `G` has cofinal compact open subgroups, `c : A →* Subgroup.center G`
is continuous, and `ι = (Subgroup.center G).subtype.comp c : A →* G`.
`R` and `S` are actual finite-length smooth complex representations of `G`, both
admissible, with equal classes in the exact finite-length Grothendieck group.
The main theorem introduces exactly these hypotheses. Its two directions are
the same lemma, applied once to `(R, S)` with the class equality and once to
`(S, R)` with its symmetric form. Each application uses admissibility only of
its target representation.

## Scalar characters of simple representations

The lemma
`ExactClassCentralSpectrumProof.apply_eq_smul_of_isGeneralizedEigencharacter`
treats an irreducible representation `ρ` of a monoid `G` (Mathlib's
`Representation.IsIrreducible`, simplicity of the lattice of
subrepresentations), a homomorphism `ι : A →* G` with central image, and a
generalized eigencharacter `χ` of `ρ.comp ι`. It proves that `ρ (ι a)` acts by
the scalar `χ a` on the whole carrier, for every `a`.

The generalized eigencharacter supplies one power `k` and one nonzero vector `w`
with `w` in the generalized eigenspace of order `k` of each `ρ (ι a)` for the
value `χ a`. Mathlib's `Module.End.hasEigenvalue_of_hasGenEigenvalue` then
makes the ordinary eigenspace of `ρ (ι a)` for `χ a` nonzero. Because `ι a` is
central, this eigenspace is the published subrepresentation
`CentralEigenspaceSplitting.eigenSubrep`. By simplicity it is the top
subrepresentation, so every vector is a `χ a`-eigenvector. The argument uses
neither Schur's lemma nor admissibility nor finite dimension of the carrier.

## One direction

The lemma
`ExactClassCentralSpectrumProof.isGeneralizedEigencharacter_of_ofRepresentation_eq`
assumes that `χ` is a generalized eigencharacter of `R.representation.comp ι`.
It proves the same for `S`, using admissibility of `S` but not of `R`.

1. **Detection in an actual simple factor of `R`.** Finite length gives actual
   composition series `s` of `R` and `t` of `S`
   (`MultiplicityAdditivityProof.exists_series`), whose graded quotients are
   irreducible. The published
   `RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter` gives an
   index `i` such that `χ` is a generalized eigencharacter of the central action
   on the actual graded quotient `s.gradedRepresentation i`. Its proof first
   finds the step where a generalized vector enters the filtration. It then
   projects that vector into the graded quotient, keeping the same uniform
   power `k`. By the previous section, `ι a` acts on this simple factor by
   `χ a`.

2. **Matching the genuine simple label in `S`.** Applying the published
   integral factor-count map `IrreducibleGrothendieckProof.factorMap` to the
   class equality and rewriting with `factorMap_ofRepresentation` and
   `compositionFactors_eq_series` equates the finite label sums `seriesClass s`
   and `seriesClass t`. These are sums of genuine irreducible isomorphism
   classes. Evaluating both at the label of the factor from step 1, via
   `seriesClass_apply`, gives equal actual factor counts
   `s.factorMultiplicity` and `t.factorMultiplicity` for that factor. Thus all
   multiplicities in arbitrary exact relations, including nonsplit extensions
   and repeated factors, are compared, with no splitting or equivalence
   `R ≃ S`. The count for `s` is positive, witnessed by `i` and the identity
   equivalence, so some graded quotient `t.gradedRepresentation j` of `S` has an
   actual representation equivalence to the factor of step 1. The published
   `CentralEigenspaceSplitting.apply_eq_smul_of_equiv` transports the scalar
   action: `ι a` acts by `χ a` on `t.gradedRepresentation j`.

3. **Recovery in the admissible representation `S`.** The actual invariant
   subspace `U = t.subrepresentation j.succ` of `S` and the surjective graded
   projection `q = (t.gradedProjection j).hom` onto
   `t.gradedRepresentation j` form a scalar subquotient. The target is
   nontrivial because an irreducible representation has a nonzero vector
   (`CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible`). Equivariance
   of `q` and the scalar action of step 2 give
   `q (U.toRepresentation (c a) u) = (χ a : ℂ) • q u`. The published
   `admissibleCentralSubquotient` (at universes `uG, uA, uV, uV`) is applied to
   `S`, `U` and `q`. It needs admissibility only of the ambient `S`, not of the
   subquotient, and its second clause gives a nonzero ordinary
   `χ`-eigenfunctional for the full transpose dual of `S.representation.comp ι`.
   The published `admissibleCentralDualToPrimal`, again using admissibility of
   `S`, converts this into the conclusion: one power and one nonzero vector of
   `S` killed by that power of `S (ι a) - χ a` for every `a`.

Uniform powers are preserved at each stage where they are carried: step 1 keeps
the power of the given vector, and the final conclusion is the uniform-power
predicate `IsGeneralizedEigencharacter` itself. The power produced for `S` is
not claimed to equal the power for `R`. This matches the statement, which
compares occurrence of characters only.

The zero representation needs no separate case. A composition series of zero
length has no graded quotients, so step 1 cannot detect a character, and indeed
no nonzero vector exists. The argument assumes no distinct characters, central
semisimplicity, multiplicity one, finite-dimensional carriers, irreducibility
of `R` or `S`, global scalar central action, decomposition, or equivalence
between `R` and `S`.

## Provenance and dependencies

This is project-internal derived algebra for the internal interface formulated
by Worker 320 and stated by Worker 34 (statement task
`e8149465-30f4-40da-99ed-948cc3fd0890`). It is not a transcription of a
literature result. The detection, matching and recovery outline follows the
possible route described in the task context. The scalar-character lemma and
the assembly are new here.

The proof imports only the following modules:

- the statement module;
- `Smooth.IrreducibleCompositionFactors`, for exact-K0 composition factors and
  genuine irreducible labels;
- `Filtration.GeneralizedEigencharacterProof`, for detection in graded
  quotients;
- `Filtration.CentralEigenspaceSplitting`, for central eigenspace
  subrepresentations and transport of scalars along equivalences;
- `Exponents.AdmissibleCentralSubquotientProof` and
  `Exponents.AdmissibleCentralDualToPrimalProof`, for admissible recovery.

It deliberately avoids `Exponents.ScalarGeneralizedEigencharacterProof`, whose
imports include a classification module.

A declaration-level audit in development traversed every constant used by the
type and proof of `Langlands.exactClassCentralSpectrum`. It found constants from
the Library's generic `Representation.Category`, `Compact`, `Filtration`,
`Smooth`, `Exponents` and `LinearAlgebra.EigenvectorDefect` modules, and from
`VirtualRepresentation.Integral`. From `Exponents.Jacquet` it found only the
generic character-space predicates and the lemmas `mem_characterSpace` and
`isGeneralizedEigencharacter_iff`. No constant comes from a `Classification`,
`Induction` or `Jacquet.*` module, and none is a GL-group, Aubert or
parabolic-induction theorem. The proof uses no conclusion of task
`aca8805b-054f-4d56-8045-12db7f623404`. This is an algebraic invariant. It
asserts no Aubert identity and no analytic square-integrability criterion.

## Validation, review and publication

The prescribed environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The
development check `b10d79cc-a4ba-47e7-9fdb-13e1babf4649` compiled the module with
zero errors and warnings. Development inspection
`a1c49574-e279-4383-93a9-307117b9854a` reports a theorem with level parameters
`uG`, `uA`, `uV` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. These are development results only. Acceptance additionally
requires the candidate's own Lake build and exact-target checks, independent
semantic review and Library publication.
