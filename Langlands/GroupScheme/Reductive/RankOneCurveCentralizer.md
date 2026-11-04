# Positive roots from a quotient curve and whole-torus centralizer containment

This internal assembly combines regular integral symmetrization, the prescribed
homogeneous-quotient curve construction, and the rank-one fixed-point sign
embedding. It introduces no new external structural assertion.

The field `k : Type u` is algebraically closed, with arbitrary characteristic.
The ambient group `G` is connected reductive. The supplied subgroup `b : B ⟶ G`
is closed, solvable and proper in the sense `¬ IsIso b`. A split maximal torus
factors as `t ≫ b`; any two of its actual roots are integrally dependent.
The normalizing rational point `n` has a nonidentity class in the actual relative
Weyl quotient. Containment of the whole-torus centralizer in the range of `b`
is an inequality of subgroup functors on every relative scheme test.

The supplied quotient projection `q : G.X ⟶ Q` is smooth, surjective and
quasi-compact, its target is separated, and its fibers obey the exact right-coset
law on every test: `q(g) = q(h)` if and only if `g⁻¹ * h` belongs to the range
of `b`. The normal-solvable-torus statement remains an explicit structural
premise. None of these inputs is constructed by this module.

`regularSignedCurveUnipotentData` first applies `regularRefinement` to the
original cocharacter `ν`, then subtracts its normalizer translate. The resulting
cocharacter is generic, so its dynamic centralizer equals the whole-torus
centralizer. The supplied containment therefore suffices for
`signedCurveUnipotentData` when the actual topological Krull dimension of `Q`
is at most one. Its result includes a selected sign, an actual smooth connected
affine unipotent representative of that signed dynamic subgroup, and the moving
quotient-curve orbit data. The selected sign is obtained by the existing
constructor, rather than supplied by the caller.

`positive_roots_eq_of_rankOne_curve_torusCentralizer` applies the existing curve
root-uniqueness theorem to the refined cocharacter. Its symmetrized dynamic
centralizer containment follows from the same equality with the whole-torus
centralizer. Every root positive on the original `ν` remains positive on the
refinement by `regularRefinement_pos`, so the conclusion concerns the original,
possibly nonregular cocharacter. The subsequent normalizer symmetrization
doubles the refined integer root pairings; no division by two or restriction
on the field characteristic is used.

`positive_roots_eq_of_rankOne_quotient_three_fixedPoints` also assumes conjugacy
of maximal tori inside `B` and the explicit implication that dimension at least
two produces three distinct rational quotient points fixed in the all-test
sense. Whole-torus centralizer containment gives the rational centralizer
containment used by the existing fixed-point sign embedding. That embedding
maps every fixed rational point into `Bool`, so three distinct such points
are impossible, forcing dimension at most one. The curve theorem then applies.
The dimension is Mathlib's `topologicalKrullDim`, valued in `WithBot ℕ∞`;
the lower-bound input is an actual embedding of `Fin 3` into fixed points.

These are conditional helpers. They do not establish the normal-solvable-torus
statement, centralizer containment, a nonidentity normalizer, torus conjugacy,
quotient existence or properness, the projective fixed-point dimension theorem,
or the final all-field positive-root uniqueness statement. In particular the
three-fixed-point implication is retained and has not been inferred from
properness alone. Provenance is the composition of the named internal Library
constructions and elementary restriction of a subgroup-functor inequality.
