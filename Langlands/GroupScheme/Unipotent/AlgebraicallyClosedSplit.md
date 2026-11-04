# Represented split series for unipotent groups over algebraically closed fields

Worker 1448. This derived assembly applies the published theorem
`Unipotent.algebraicallyClosedSplit_of_oneDimensional` to the published
proofs `unipotentClosedSubgroup` and
`perfectFieldOneDimensionalUnipotent`. Its provenance is internal composition
of these three Library results, imported by their Lean module names.

For every algebraically closed field `k : Type u` and every group scheme `U`
over `Spec k`, `algebraicallyClosedSplit` assumes smoothness and affineness
of the structure map, connectedness of the underlying space, and the
existing fixed-vector predicate `IsUnipotent U`. It concludes the unchanged
`RelativeRoot.IsSplitUnipotent U`. There is no characteristic restriction
and no chosen series, quotient, embedding or classification premise.

The result includes an actual finite series in
`RelativeRoot.HasSplitSeries`: each successor uses a represented fppf
quotient with one-dimensional vector-group coordinates, and the terminal
condition is triviality on every relative scheme test. The length-zero
case supplied by the imported reduction includes the trivial group.

`algebraicallyClosedSeries` chooses a natural-number length with the full
`RelativeRoot.HasSplitSeries` proof at that length. It specializes the
published conditional choice `algebraicallyClosedSplitSeries` using the
same two proofs. Both declarations retain precisely the geometric and
unipotence hypotheses above.

The implemented proof only substitutes these published inputs. The
reduction uses proper smooth closed-subgroup induction, the reduced
identity component of an additive-character kernel, its actual represented
quotient, and the one-dimensional classification. This module adds no new
geometric argument. It supplies the unconditional unipotent callback needed
by the algebraically closed solvable-group reduction. The general solvable
torus-quotient input and the full solvable-group theorem remain separate
obligations; the stronger statement over every perfect field is unchanged.
