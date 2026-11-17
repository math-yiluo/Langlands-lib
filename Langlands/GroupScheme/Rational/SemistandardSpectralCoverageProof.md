# Semistandard parabolic coverage

Worker 770, Task 7514. This proves exactly
`Langlands.GroupScheme.SemistandardSpectralCoverageStatement.{u}`. The source
motivation is Waldspurger (2003), I.1, printed p.238, registered as
`waldspurger-2003-plancherel`; original PDF pages 4–5 were read. The arbitrary-field
scheme-theoretic assertion is the published Library target, extending the source's
local-field point notation through the existing group-scheme theorems.

`IsParabolicFunctor.exists_fixedTorusCocharacter` is a derived helper. Choose an
actual parabolic representative and use `parabolicDynamic` to present it by a
ground-field cocharacter. Factor the fixed torus through this representative.
The factor remains maximal split by `IsMaximalSplitTorus.of_comp`. The parabolic
is smooth, affine and connected: smoothness and closedness come from its
parabolic predicate and connectedness from `dynamicConnected`. Inside this
smooth connected affine group, `exists_innerIso_comp_eq_cocharacter`, with its
premise discharged by `smoothMaximalSplitTorusConjugacy`, conjugates the presenting
cocharacter into the fixed torus. Naturality of inner conjugation sends this
equality into the ambient group. The conjugating rational point belongs to the
original parabolic, so `DynamicLeviConjugacy.parabolic_comp_innerIso_eq` preserves
that actual parabolic. The result is equality on every test scheme with a
cocharacter of the specified torus, rather than only rational conjugacy.

`semistandardSpectralCoverage` applies this helper to each target parabolic and
uses `SemistandardSpectralIndex.ofCocharacter`. Its connected reductive Levi,
geometric radical and all-test decomposition are supplied by that published
constructor, whose structural inputs are already proved. Subtype equality gives
the exact surjectivity conclusion.

The field and universe are arbitrary, and the ambient group is connected
reductive with a maximal split torus. No maximal absolute torus, split ambient
group, local-field restriction, extra realization premise or finiteness claim
is introduced. The target and all its imported pairs are unchanged.
