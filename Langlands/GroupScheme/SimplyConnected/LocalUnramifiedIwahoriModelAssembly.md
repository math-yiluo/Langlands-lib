# Conditional construction of the model of a stable chamber

This internal construction specializes
`IntegralModel.exists_descendedStableParahoricModel` to a chamber of the
supplied building of the unramified extension of a simply connected group.
The arbitrary universe `u`, original group, building, semilinear action and
chamber are retained.

The inputs still include proofs of `UnramifiedParahoricModelStatement` and
`IntegralModel.UnramifiedSmoothModelDescentStatement`, and the assertion that
every rational point stabilizing the specified chamber setwise fixes it
pointwise. The file does not prove these inputs or the unconditional host
statement `LocalSimplyConnectedUnramifiedIwahoriModelStatement`.

The proof first applies `isSimplyConnectedFieldExtension` to obtain simple
connectedness over the actual maximal unramified field. Its semisimplicity
implies connected reductivity, so
`UnramifiedZeroDatum.ofConnectedReductive` constructs the zero datum.
`MaximalUnramified.isChamber_exists_bounded` supplies a presentation of the
chamber as a translated image of a nonempty apartment subset bounded above
under every real affine functional. These discharge the algebraic-choice and
boundedness premises of the general conditional parahoric assembly.

That assembly provides a smooth integral model over the original integers,
connectedness of its full special fibre and an equivalence between membership
in its unramified integral-point image and full setwise stabilization of the
original chamber. `localUnramifiedIwahoriModelOfInputs` chooses that model;
its three specification lemmas retain these conclusions.

`localSimplyConnectedUnramifiedIwahoriModel_of_inputs` quantifies the
pointwise-fixation input over all the original fields, simply connected groups,
supplied buildings and chambers. Together with the two general model
statements, it implies exactly
`LocalSimplyConnectedUnramifiedIwahoriModelStatement.{u}`. Its proof introduces
the unchanged target's arguments and applies the chamber construction. The
connected-special-fibre predicate unfolds to the actual `ConnectedSpace`
expression in that target. All three global proof inputs remain explicit.

The provenance is internal composition of the named Library interfaces and
helper theorems. No additional literature claim or independence of the chosen
model is asserted.
