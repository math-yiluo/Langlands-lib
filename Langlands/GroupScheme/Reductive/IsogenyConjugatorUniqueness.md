# Uniqueness of actual adjoint-torus isogeny conjugators

Worker 689.

This internal derived development separates existence from uniqueness in the
published `SplitIsogenyUniquenessStatement`. Its proposition
`SplitIsogenyConjugatorExistenceStatement` repeats exactly the published
hypotheses and the actual group-scheme equality, replacing unique existence
only with existence of the specified adjoint-torus ground-field point.
It retains arbitrary fields, general isogenies, full character equality,
central torus directions and the supplied actual adjoint quotient and torus.
The final theorem proves that this existence-only statement implies the
unchanged published uniqueness statement.

The implemented uniqueness proof first proves that equality of two actual
maps obtained by composing an isogeny with the evaluated inner actions
forces equality of the acting adjoint rational points. It evaluates the
map equality on all relative tests, identifies evaluation with the
all-test inner action, and applies
`IsAdjointQuotient.innerAction_point_ext_of_isogeny`. That theorem uses
flat local lifts along the isogeny, so it covers inseparable isogenies and
nonsmooth kernels. It uses the full scheme-theoretic centre.

The actual inclusion of the supplied adjoint torus is a closed immersion,
hence a monomorphism. Cancellation along this inclusion then proves
`IsAdjointSplitTorusImage.conjugator_point_unique`.
`existsUnique_conjugator_of_exists` supplies the exact unique-existence
conclusion from any such rational conjugator. Neither lemma assumes that
the rational point lifts to a rational point of the original torus.

The provenance is internal: these are formal consequences of the actual
adjoint inner action, its all-test faithfulness, base-point evaluation,
and the published adjoint-torus image predicate. This unit proves
uniqueness and the reduction to existence; it does not assert unconditional
existence of a conjugator.
