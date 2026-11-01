# Standard rational refinement transfer

Author: Worker 146. This is a conditional consequence for the unchanged
whole-spectrum scalar gluing proof. It imports the published
`ScalarCoverDescent` and `StandardRationalCover` modules.

`existsUnique_whole_gluing_of_standard_refinement` takes the explicit
premise of unique scalar gluing for every standard rational cover over every
presented strict affinoid base over the fixed coefficient field. It applies
the published `ScalarCoverDescent.of_refinement` to a standard rational
refinement of the given family of actual rational quotients.

That transfer requires separation on the pullback refinement over each
original quotient. Pulling a standard datum back along its actual base map
is definitionally the standard datum for the mapped tuple. The published
`tuple_no_common_zero_pullback` supplies the no-common-zero condition there.
Applying the standard-cover premise to that quotient base and the published
`ScalarCoverDescent.separated` gives precisely the required local separation.
This step is essential for recovering every original section.

The common-target compatibility and general refinement arguments originated
in Worker 146's earlier private adapter. Worker 572 extracted them into the
published `ScalarCoverDescent`, adding explicit predicates and other formal
transport results; both workers are credited in its paired Markdown.
This module imports those proofs by their published Lean names and retains
only the standard-cover specialization. The implemented general transfer
and its internal provenance are described in
[`ScalarCoverDescent.md`](ScalarCoverDescent.md).

The specialization preserves the coefficient universe, zero and nonreduced
bases, trivial scalar norms, empty index types and empty rational loci. The
original family index universe is independent of the coefficient universe;
the standard refinement is indexed by `Fin n`. The analytic standard-cover
premise and existence of the geometric refinement remain separate inputs.
The final application in `WholeSpectrumRationalGluingProof` supplies the
standard-cover premise and the geometric refinement with their proved Library
theorems. This adapter itself asserts no higher Cech exactness, admissibility,
arbitrary-radius result or categorical sheaf theorem.
