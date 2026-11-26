# Word estimates for lifts along open smooth quotient maps

`le_topologicalClosure_smoothKFinite_inf` proves density of the compact-finite part
of a closed, orthogonal-invariant subspace of genuine smooth vectors. A compact
weighted average of a vector of the subspace belongs to the subspace because all
continuous linear functionals vanishing on it vanish on the average. This uses the
published formula for scalar evaluations of compact smooth averages and Hahn–Banach
separation for closed submodules. Averaging against polynomial weights produces
compact-finite vectors because those weights have finite translation spans. A
continuous linear functional vanishing on the closure of the compact-finite part
therefore has all polynomial integrals of its scalar orbit coefficient zero. The
polynomial separation lemma on `O(n)` makes the coefficient vanish, in particular
at the identity, which proves the density claim.

`RealSmoothQuotientWordLiftStatement` assumes a continuous open linear map between
the genuine smooth carriers of representations of `GL_n(ℝ)` that intertwines the
orthogonal actions. The source action is jointly continuous and its normed carrier
`E` has the explicit instance `[CompleteSpace E]`. The target carrier is a complex
normed space. Every compact-finite vector of the target is assumed to have at least one
compact-finite lift. For every finite sum of source word seminorms the proposition
supplies a finite sum of target word seminorms and a nonnegative constant that
control the size of a compact-finite lift of each compact-finite target vector.

`realSmoothQuotientWordLift` begins with the open image of the unit ball for the
chosen sum of source word seminorms. It contains a neighborhood defined by finitely
many target words. Add the empty word to the controlling sum, which then vanishes
only at zero. A nonzero target vector can be scaled to enter the image of the unit
ball. There is a compact-finite lift inside that ball. Indeed, subtract any known
compact-finite lift from a smooth lift in the ball and approximate the difference
by compact-finite vectors of the kernel. This kernel is closed and orthogonal
invariant, so the density lemma applies. Rescaling the lift gives the estimate.

This is the topological part of the quantitative lift for smooth quotient maps,
derived from the usual neighborhood and density argument. The assumption of
openness supplies the neighborhood comparison used in the proof.
