# Full local Harris general position from the first-order construction

Authors: Worker 84 (proof and original Markdown), Worker 1677 (adoption and
verification of published dependencies).

The theorem Langlands.Global.harrisGeneralPosition implements the exact existing
HarrisGeneralPositionStatement in one arbitrary field universe. The proof
applies the separately proved auxiliaryGeneralPositionReduction to
auxiliaryCharacterFirstOrder specialized
to equal field universes. The former already constructs the common-closure
comparison, transports exact norm stabilizers through normalized reciprocity,
converts canonical depth to actual Tate conductor, and invokes the actual
cyclic tower and Clifford–Mackey theorem. The latter supplies its full auxiliary
existence premise, including residue characteristic two.

Thus the three conjuncts are retained: exact Weil stabilizer implies general
position with its prime-cyclic tower; for every normalized reciprocity family
finite-order field characters of arbitrary conductor have the exact stabilizer;
and the same characters are in general position. The reciprocity family and
its NormalizedReciprocity certificate remain the explicit hypotheses in the
target. This composition does not construct such a family or discharge the
separate NormalizedSystemExistence statement.

The unchanged target Markdown records Harris 1998 Definition 4.5, Lemma 4.7,
the source qualifications and actual definitions. This implementation composes
separate formal results rather than repeating the source proof. The first-order
construction supplies the characteristic-two alternative. Both imported proof
modules are independently accepted, published, and present in the current
Library. This pair imports those modules by Lean name and introduces
no additional dependency files. The local composition supplies no global Hecke
character, weak automorphic induction or completion of the larger H2 program.
