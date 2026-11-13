# Henniart's candidate existence from its global inputs

This module declares the **statement**
`Langlands.Henniart.CandidateExistenceReductionStatement`, with universe
parameters `uK uW uP uE uQ`. It is a proposition definition, and the file
contains no proof of it. It is the assembly unit of the H3 program (Henniart's
global construction, task `34b81620-20d7-4059-9b08-6bedd1c1c029`). It states
that the published local target `CandidateExistenceStatement` follows from the
remaining open inputs of Henniart's global construction. Its provenance is
*derived*: Henniart's §3 has no single statement of this form. The statement
records how his argument combines its inputs, as listed in §3 below.

## 1. The statement

The proposition is an implication with five hypotheses:

1. `Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP}`: Harris (1998),
   Proposition 4.8, at the levels used by the published
   `HenniartGlobalizationStatement`.
2. `ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`:
   Henniart (2000), Théorème 2.4, for number fields in `Type`.
3. `ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0}`: local
   finite-level class formation with its fundamental classes, for p-adic fields
   in `Type`.
4. `Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uW, uP}`:
   the certified local pole comparisons of Henniart's Lemme 2.8, for number
   fields in `Type`.
5. `Global.PoleComparison.HenniartCompositeMapStatement.{0, uK, uW, uP, uE}`:
   the composite map built from a generated positive isometry at `F_v` has all
   properties of Henniart's 3.8 at every `K ≅ F_v`.

Its conclusion is `CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`. For every
prime `p`, every p-adic field `K` in universe `uK`, and every homomorphism `q`
from the absolute Galois group of `K` to a finite group `Q` in universe `uQ`,
there is a candidate at `q`. A candidate is a `ℤ`-linear equivalence
`Φ : W ≃ A`. Here `W` is a submodule of the unitary Weil lattice of `K`
containing every unitary class that factors through `q`. `A` is a submodule
of the unitary supercuspidal lattice of `K`. `Φ` has every property of
Henniart's 3.8 (`LatticeMap.HenniartProperties`).

## 2. Universe levels

The global construction (`RelativeGaloisGlobalization`) produces number fields
in `Type`. The supercuspidal lattice of a completion `F_v` therefore lives in
universe `0`. So the conclusion fixes the automorphic-lattice universe of
`CandidateExistenceStatement` to `0`. Every other universe is free: the
p-adic field universe `uK`, the Weil carrier universe `uW`, the
spectral-presentation universe `uP`, the epsilon-system universe `uE` and the
finite-quotient universe `uQ`.

The local correspondence results in `Langlands/Correspondence/` use
`CandidateExistenceStatement` with an arbitrary automorphic universe `uV`.
Getting there from universe `0` is a separate carrier-universe transport. It
is not part of this statement. That transport is the work of Worker 5732,
Task 5583.

## 3. Source correspondence

The source is G. Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455
(`henniart-2000-simple-proof`). PDF page = printed page − 438.

- **§2.7, step 1, p.447 (PDF 9), and Théorème 3.1, p.448 (PDF 10).** Fix a
  finite Galois extension of the local field, here given by `q`. There are a
  number field `F`, a place `v` and an isomorphism of `F_v` with the local
  field such that the image `R_G(F, v)` contains every element factoring
  through that Galois group. "Le Théorème 2.5 donne alors un candidat." In the
  Library this is `RelativeGaloisGlobalization`. The proved
  `henniartGlobalization_of_inputs` derives it from hypotheses 1 and 2,
  together with inputs that are already proved.
- **Théorème 2.5 and Lemme 2.8, pp.446–448 (PDF 8–10).** These give the
  isometry `R_G(F, v) ≅ R_A(F, v)`. In the Library, hypothesis 4 together
  with the proved `relativePolePairing` gives a unique
  `RelativeGeneratedPositiveIsometry`.
- **§§3.7–3.8, printed p.451 (PDF 13).** These define the composite map
  `R_E(F) → R_A(F)` at the local field. Its properties (a)–(c) follow "par
  transport de structure, grâce à 2.6". In the Library this is hypothesis 5,
  for the composite map along `K ≅ F_v`. The published
  `CandidateExistenceStatement` cites Théorème 3.1 with §§3.7–3.8, and the
  present conclusion is that statement.
- **Fundamental classes.** Henniart uses global class field theory throughout
  §2. In the Library the relative Weil groups need an arithmetic fundamental
  class family. Hypothesis 3 with the proved `globalFundamentalClassStatement`
  supplies one.

## 4. The expected proof

A private development check compiled the following route in full. The route is
recorded here for the proof task; this unit does not prove the statement.

1. Choose an invariant family from hypothesis 3. By
   `globalFundamentalClassStatement.{0}`, this gives a class family `c` with
   `IsArithmeticClassFamily c`.
2. Apply `henniartGlobalization_of_inputs` to `p`, `K` and `q`. Its other
   inputs are the proved `commonClosureReciprocityExistence`,
   `localInducedRestriction`, `associatedCentralCharacter` and
   `localTransferReciprocity`, plus hypotheses 2 and 1. The result is `F`,
   `E`, `v`, `h` and `f` with the covering property.
3. Use `compactSpace_adeleQuotient F`, and take as `ψ` the standard finite
   additive component of `F` at `v`
   (`HeckeFunctionalEquation.standardFiniteAdditiveComponent`).
4. Hypothesis 4 and `relativePolePairing` give the isometry `T`. Hypothesis 5
   gives `HenniartProperties` of `henniartCompositeMap F E c v h K f T`.
5. The domain condition follows from the covering property and
   `continuousRestrict_completionWeilTransport_eq_iff`.

**Known obstruction (Library at `730bd1f2`).** The name
`Langlands.Automorphic.OperatorRealization.evaluate_toContinuous_smul` is
declared both in `Langlands/Automorphic/CuspidalAdmissible/Reproduction.lean`
and in `Langlands/Automorphic/OperatorScalarCentralCharacter.lean`.
`HenniartGlobalizationReduction` imports the first and
`AssociatedCentralCharacterProof` imports the second. So no module can import
both. The development check compiled after marking the second copy `private`;
the statements are identical, and its only uses are in its own file. This
statement module imports neither of them.

## 5. Scope

- No hypothesis is a consequence of another. Each of the five is an open
  Library target with its own owner, or is owned by this program.
- The conclusion concerns candidates only. Independence of choices
  (`ChoiceIndependenceStatement`) and the final correspondence are separate
  targets.
- The statement asserts nothing about uniqueness of the candidate, and nothing
  for finite quotients of the Weil group that do not come from the Galois
  group.
