# Effective descent of one represented filtration step

This internal construction combines the Library's effective descent of invariant
closed subgroups with its effective descent of supplied affine fppf quotients.
It supplies a geometric successor step for the relative unipotent filtration.

Let `p : S → B` be a flat surjection between affine schemes, let `H` be an affine
group scheme over `B`, and supply an inclusion `i : N → H_S` and a homomorphism
`q : H_S → Q`. Assume `i` is a closed subgroup, `N` and `Q` are smooth over `S`,
`Q` is affine, and `q` is the actual fppf quotient by the full represented range
of `i`. The all-test ranges of the two pullbacks of `i` must agree on the double
overlap, after the canonical ambient overlap isomorphism.

`FiltrationStepDescentData` records group schemes `K` and `V` over `B`, a smooth
closed normal inclusion `j : K → H`, and a represented fppf quotient
`r : H → V`. Both `K` and `V` are affine and smooth over `B`. It retains actual
recovery isomorphisms `K_S ≅ N` and `V_S ≅ Q`, with the exact equations
`j_S = eK.hom ≫ i` and `r_S ≫ eV.hom = q`. The quotient's full scheme-theoretic
kernel has the same subgroup functor as `j`.

`nonempty_filtrationStepDescentData` constructs these data. First the existing
`IsClosedSubgroup.exists_descent_of_overlap_range_eq` supplies `K`, `j`, and its
recovery map. The range of `j_S` equals the range of `i` because their sources
are isomorphic. The existing `Descent.exists_affine_fppfQuotient` therefore
constructs `V`, `r`, and the second recovery map from the supplied `q`. Its
quasi-compactness requirement follows from the affine source and target. This
uses the actual quotient descent datum constructed from the ambient and kernel
data; no effective descent solution or quotient existence premise downstairs
is added.

Smoothness transports through each recovery isomorphism and reflects along the
fpqc cover using Mathlib's `Smooth` descent theorem. The affine cover is
quasi-compact. Normality follows directly from the full kernel equality: the
points killed by a group homomorphism are closed under conjugation on every
test. This argument does not need a separate local normality assumption.

`filtrationStepDescentOfOverlap` chooses the constructed data. The final theorem
`FiltrationStepDescentData.hasVectorBundleSeries` extends a supplied series on
`K` by this geometric step when `V` is proved to satisfy the existing actual
`IsVectorBundleAdditive` predicate.

The construction works in arbitrary universe `u`. It assumes no noetherian,
connectedness, nonempty-base, or constant-rank hypothesis. It does not deduce
linearity of quotient transitions from additive group isomorphisms. Constructing
the local filtration, proving overlap invariance, providing actual linear
quotient charts, and proving termination remain obligations of the parent task.
The provenance is internal composition of the cited Library declarations and
Mathlib's fpqc smoothness reflection, rather than a new external-source claim.
