# Assembly of Popescu's theorem from its lemmas

`popescuFactorization_of` proves `PopescuFactorizationStatement.{u}`, the
finite-type factorization form of Popescu's theorem (Stacks Project, *Smoothing
ring maps*, Theorem 12.1, tag 07GC). It takes six Library statements as
hypotheses:

- `SingularIdealFactorizationStatement` (Lemma 2.8, 07EU);
- `NilpotentLiftingStatement` (Proposition 5.3, 07CM);
- `StrictlyStandardDesingularizationStatement` (Lemma 7.3, 07F0: desingularization
  along a strictly standard element);
- `CharZeroResolutionStatement` (Lemma 10.3, 07FE);
- `CharPResolutionStatement` (Lemma 11.4, 07FJ);
- `LocalizationStandardDescentStatement` (Lemma 8.3, 07F4).

Proof:

1. Let `C` be a finite type `R`-algebra and `f : C → S` an `R`-algebra map.
   Since `R` is Noetherian, `C` is finitely presented over `R`
   (`Algebra.FinitePresentation.of_finiteType`).
2. `fieldCase_of_resolutions` (module `FieldCaseAssembly`) derives the field case
   `PopescuFieldCaseStatement` from Lemmas 2.8, 10.3 and 11.4.
3. `reductionToField_of` (module `ReductionToFieldAssembly`) derives property PT
   (`HasSmoothFactorizations R S`) for every regular map of Noetherian rings
   from the field case together with Lemma 2.8, nilpotent lifting, the
   desingularization step and Lemma 8.3.
4. Applying property PT to `f` gives the factorization `C → B → S` through a
   smooth `R`-algebra `B`.
