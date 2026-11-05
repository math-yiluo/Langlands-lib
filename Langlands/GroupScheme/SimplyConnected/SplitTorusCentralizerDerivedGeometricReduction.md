# Reduction of the centralizer-derived theorem to algebraically closed fields

Author: Worker 1366.

This is an internal reduction for
`SplitTorusCentralizerDerivedSimplyConnectedStatement`, with two explicit
remaining hypotheses. It does not prove that statement unconditionally.

`IsSplitTorus.isClosedSubgroup_torusCentralizer` proves that every supplied
representative of a split-torus centralizer in an affine locally finite-type
field group is a closed subgroup. The torus homomorphism itself need not be
closed, and the ambient group need not be smooth or reductive. The proof uses
the existing `centralizingCocharacter`: its dynamic centralizer is the full
torus centralizer on every test scheme. The closedness theorem for every
representative of a dynamic centralizer then applies.

`SplitTorusCentralizerDerivedSimplyConnectedAlgClosedStatement.{u}` is the
public target restricted to algebraically closed fields in the same arbitrary
universe. It quantifies over a simply connected group, a split subtorus, every
representative of its all-test centralizer, and every actual closed derived
subgroup of that representative. It asserts that this derived subgroup is
simply connected. This proposition definition is not a proof.

`splitTorusCentralizerDerivedSimplyConnected_of_algebraicClosure` assumes
`IsSimplyConnectedAlgebraicClosureAscentStatement.{u}` and the preceding
restricted proposition, and concludes exactly
`SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}`.

The implemented proof establishes closedness of the supplied centralizer
inclusion by the first lemma and hence affineness of its source. It base
changes the original group, split subtorus, centralizer inclusion and derived
inclusion to the algebraic closure of the original field. Splitness and
closedness of the torus inclusion are preserved. The all-test centralizer
commutes with base change by `torusCentralizer_baseChange`, so the supplied
centralizer representative also base changes correctly. The full
scheme-theoretic derived subgroup commutes with this affine base change by
`derivedSubgroup_baseChange_eq_of_field`, which carries the supplied derived
inclusion to an actual derived inclusion.

The ascent hypothesis supplies simple connectedness of the ambient group over
the algebraic closure. The restricted hypothesis then proves simple
connectedness of the base-changed derived group. The already proved
`IsSimplyConnected.of_algebraicExtension` descends that conclusion, including
semisimplicity, to the original derived group. No additional semisimplicity
premise on the original derived group is used.

The provenance is an elementary reduction of the exact published target using
the imported, proved base-change and reflection APIs. The two displayed
hypotheses remain structural proof obligations.
