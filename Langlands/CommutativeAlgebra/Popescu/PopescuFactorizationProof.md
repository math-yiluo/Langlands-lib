# Proof of Popescu's theorem (finite-type factorization form)

`popescuFactorization` proves `PopescuFactorizationStatement.{u}`. This is the
finite-type factorization form of Popescu's theorem (Stacks Project, *Smoothing
ring maps*, Theorem 12.1, tag 07GC). Let `R → S` be a regular algebra map of
commutative Noetherian rings and `C` a finite-type `R`-algebra. Then every
`R`-algebra map `C → S` factors as `C → B → S` through a smooth `R`-algebra `B`
in the same universe.

## Proof

The theorem applies `popescuFactorization_of` (module
`Langlands.CommutativeAlgebra.Popescu.FactorizationAssembly`) to the following
six theorems, all published in the Library:

| Hypothesis | Library theorem | Stacks reference |
| --- | --- | --- |
| `SingularIdealFactorizationStatement` | `Popescu.singularIdealFactorization` | Lemma 2.8 (07EU) |
| `NilpotentLiftingStatement` | `Popescu.NilpotentLifting.nilpotentLifting` | Proposition 5.3 (07CM) |
| `StrictlyStandardDesingularizationStatement` | `Popescu.Desing.strictlyStandardDesingularization` | Lemma 7.3 (07F0) |
| `CharZeroResolutionStatement` | `Popescu.charZeroResolution` | Lemma 10.3 (07FE), characteristic 0 |
| `CharPResolutionStatement` | `Popescu.charPResolution` | Lemma 11.4 (07FJ) |
| `LocalizationStandardDescentStatement` | `Popescu.localizationStandardDescent` | Lemma 8.3 (07F4) |

The assembly has three modules, which were added with this file.

- `FieldCaseAssembly` proves `fieldCase_of_resolutions`: the field case
  (`PopescuFieldCaseStatement`) follows from Lemmas 2.8, 10.3 and 11.4. The
  argument is Noetherian induction on the singular radical, in characteristic 0
  or `p`.
- `ReductionToFieldAssembly` proves `reductionToField_of`: property PT
  (`HasSmoothFactorizations R S`) holds for every regular map of Noetherian
  rings. The inputs are the field case, Lemma 2.8, nilpotent lifting, the
  desingularization step and Lemma 8.3. This is the reduction of Stacks
  Section 12.
- `FactorizationAssembly` proves `popescuFactorization_of`. A finite-type
  algebra over the Noetherian ring `R` is finitely presented, and property PT
  applied to `f : C → S` gives the factorization.

No hypothesis remains. The theorem uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
