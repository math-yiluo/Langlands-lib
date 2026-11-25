# Continuity of the literal semistandard Levi projection

`Langlands.HarishChandraSchwartz.RationalSemistandard.projectionContinuity`
proves the published `ProjectionContinuityStatement` for every field universe,
with the statement's explicit local-field, connected-reductive and
maximal-split-torus premises. The target is a derived topological formulation
of the distinguished Levi in Waldspurger (2003), §I.1, printed pp. 238–240,
registered as `waldspurger-2003-plancherel`.

`Langlands.GroupScheme.semistandardSpectralDynamicCoverage` realizes the entire
intrinsic index by a cocharacter of the specified torus. Rewriting by that index
equality identifies the literal parabolic, Levi and radical with the identity-test
points of the three dynamic subgroups, in their inherited rational-point
topologies. The two proofs of semidirect decomposition give the same projection
by proof irrelevance. `Langlands.Aubert.General.continuous_dynamic_projection`
then proves continuity through the represented dynamic subgroups and the
algebraic limit morphism. Its affine-scheme hypothesis follows from the
ambient affine morphism by `isAffine_of_isAffineHom`, and its separatedness
hypothesis follows from `IsConnectedReductive.isSeparated`.
