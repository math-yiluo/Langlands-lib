# Root containment across a chamber-simple wall

This module supplies root-fixer comparisons needed to isolate the exceptional
root ray at a chamber-simple affine wall. It uses the existing actual subgroups
of rational points, their valuations, and geometric affine reflections.

The setting has arbitrary universe `u`, a field `k : Type u`, an affine group
scheme `G`, a commutative group scheme `S`, a monomorphic inclusion
`i : S.toGrp ⟶ G`, a function `ω : kˣ → ℝ`, and `D : KPApartmentData i ω`.
Write `ψ` for an element of
`AffineRootSystem.simpleAffineRoots D.affineRoots C` and write
`s = affineReflection ψ hv.1` for its reflection, given a coroot `hv`.
Simple-root membership includes the chamber and wall hypotheses used below.
The structural hypothesis AS4 is

`∀ η ∈ D.extendedAffineRoots, η ∈ D.affineRoots ∨ 2 • η ∈ D.affineRoots`.

For a relative root `b`, a scalar `c < 0`, and derivative equality
`(c • ψ).linear = rootForm i b`, the module proves the equalities

`rootFixer b C = affineRootGroupPlus b (c • ψ)`,

`rootFixer b (s '' C) = affineRootGroup b (c • ψ)`.

Both use AS4, simple-root membership, and the stated derivative equality;
the second also uses the coroot. In particular,
`rootFixer b C ≤ rootFixer b (s '' C)`. The root direction `b` is unchanged.
These statements cover every negative real scale with an actual relative-root
derivative, without requiring that `b` be indivisible.

For the entry `negativeRootFixerReflectionInclusion`, also assume
`IsAffineRootSystemWithRankZero D.affineRoots`, a relative root `a` with
`ψ.linear = rootForm i a`, and a cocharacter `ν` satisfying
`0 < latticePairing S a ν` and `latticePairing S b ν < 0`.
The entry is a monoid homomorphism

`rootFixer b C →* rootFixer b (s '' C)`.

It is the subgroup inclusion induced by the proved containment and hence
preserves the underlying rational point. Genericity of `ν` is unnecessary
for this individual negative-root comparison.

The further positive-ray results assume a split torus `S.toGrp`, the
affine-root-system condition for `D.extendedAffineRoots`, and

`derivativeRoots D.extendedAffineRoots = Set.range (rootForm i)`.

Two roots in `RelativeRoot.indivisiblePositiveRoots i ν` whose apartment
forms are real scalar multiples are then equal. No reducedness assumption
is made on the root system. If `a₀` is such an indivisible positive root,
`ψ.linear = d • rootForm i a₀` for a real `d`, and `b` is another positive
indivisible root with `b ≠ a₀`, then

`rootFixer b C = rootFixer b (s '' C)`.

This last comparison also assumes AS4 and the affine-root-system condition
for `D.affineRoots`, as well as the simple root and coroot. The scalar `d`
does not require a separate sign hypothesis.

Finally, under AS4 and the simple-wall and coroot hypotheses, if
`ψ.linear = rootForm i a` and the actual root `a` equals `b` or `2b`, the
module proves the product inclusion

`rootFixer b C ⊆ rootFixer b (s '' C) · affineRootGroup a ψ`.

This covers the exceptional primitive ray even when the derivative `a` is
divisible. It is an inclusion of sets; no uniqueness of factors is claimed.

For the negative scaled comparisons, the simple-wall geometry supplies a
point `x ∈ C` and a point `y` in its facet closure with `ψ(y) = 0`.
The functional `c • ψ` is negative at `x`, so the negative closure-point
comparison in `ChamberWallRootGroups` identifies the chamber fixer with its
strict affine root group. The reflection fixes `y`, transports the closure
condition to `s(x)`, and makes `c • ψ` positive throughout `s(C)`. The
nonstrict closure-point comparison identifies the reflected fixer.
The existing inclusion of the strict group in the nonstrict group proves
the containment.

For the entry's general negative-root comparison, split according to
proportionality with `ψ.linear`. Pullback of the quotient forms gives
`eval S b = t • eval S a`. Evaluation on `1 ⊗ ν` forces `t < 0`; the scaled
comparison therefore applies. In the nonproportional case,
`ChamberWallFiltration` gives equality of the two fixers. `Subgroup.inclusion`
packages the resulting containment as the entry homomorphism.

For positive-ray uniqueness, the same evaluation forces the proportionality
scalar to be positive. The root-integrality argument already proved in
`ChamberExchange.eq_or_double_of_eval_eq_smul` leaves equality or doubling in
either direction. The indivisibility conditions exclude both doubling cases.
For a distinct positive indivisible root, any proportionality with the wall
would thus contradict distinctness, so `ChamberWallFiltration` applies.
For the exceptional ray, when `a = b` its chamber fixer is exactly `U_ψ`
by `ChamberWallRootGroups`, and an identity reflected factor suffices. When
`a = 2b`, the inclusion is `HalfWallRootFactorization`'s half-root inclusion.

This is derived content from the named Library interfaces and their bundled
unchanged predecessors. It introduces no external-source assertion, rank-one
factorization premise, or ordered-product premise. It does not yet assemble
the full parahoric factorization or prove `AffineIwahoriTitsStatement`; these
remain open.
