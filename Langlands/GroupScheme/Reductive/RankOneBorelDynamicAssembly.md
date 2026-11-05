# Conditional assembly of the two dynamic Borels in rank one

Worker 1301. This internal assembly composes the prescribed-Borel curve
construction with Worker 1639's homogeneous-curve parabolic comparison.
The latter adapts the contracting-subgroup argument by Workers 1549, 1547,
and 317.

The construction retains the following four structural propositions as
explicit arguments:

- `SolvableProperFixedPointStatement`;
- `ProjectiveTorusFixedPointDimensionStatement`;
- `SolvableMaximalTorusConjugacyStatement`;
- `AlgClosedMaximalTorusCentralizerStatement`.

Over an algebraically closed field in universe `u`, in every characteristic,
let `G` be connected reductive and `i` a split maximal torus embedding.
Assume pairwise integral dependence of the actual Lie roots, choose an actual
root `α`, and let `ν` be any cocharacter with nonzero pairing against `α`.
Fix a Borel embedding `b` and a factorization `t ≫ b = i`.

`prescribedBorelSignedParabolic` returns an actual cocharacter `eta`,
a proof that `eta = ν` or `eta = -ν`, and a witness that the dynamic parabolic
for `eta ≫ i` is represented by the specified `b`. The representation
witness includes monomorphism and equality of subgroup functors on every
test scheme.

The implementation first calls `prescribedBorelDynamicCurveData` with all
four structural inputs. This produces the actual proper homogeneous quotient
of the prescribed Borel, a smooth surjective quasi-compact projection with
exact all-test coset fibers, a quotient dimension bound of at most one,
containment of the original cocharacter's dynamic centralizer in the Borel,
exact rational root-span dimension one, and a nonisomorphic Borel inclusion.
Properness supplies separatedness for the curve comparison. Rewriting by
`t ≫ b = i` gives the required centralizer containment for the composed
torus map. The implementation then applies
`HomogeneousQuotient.signedParabolicRepresentativeOfCurve` to this same
quotient and Borel, and rewrites its output using the same factorization.
Thus the construction keeps the specified torus embedding and the original
cocharacter throughout.

`rankOneBorelDynamic_of_projectiveBorelInputs` introduces the public
statement's arguments, uses the selected signed representative, and splits
its signed equality to obtain the required disjunction. Its conclusion is
`RankOneBorelDynamicStatement`, but its four structural arguments remain
unproved premises. This is a conditional reduction, not an unconditional
proof of that statement and not completion of the rank-one Borel proof task.

The provenance is internal composition of the named constructions. No
additional classification theorem, root generator, or structural proof is
supplied by this module.
