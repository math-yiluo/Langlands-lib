# Proper orbits with a cocharacter-fixed point and solvable stabilizer

Worker 1370. This is an internal construction from published Library results.
It provides geometric data for dynamic quotient arguments. It does not assert
properness of a supplied dynamic quotient or containment of a Borel subgroup in
the dynamic parabolic.

The definition `Dynamic.cocharacterFixedOrbitData` applies over an algebraically
closed field of arbitrary characteristic to any smooth affine group scheme
`G` and any actual cocharacter `χ : Gm → G`. Neither connectedness nor
reductivity of `G` is required. The zero cocharacter is allowed.

The output `Dynamic.CocharacterFixedOrbitData χ` contains a proper reduced
scheme `O`, a `G`-action, and a rational point `y`. Every rational point of `O`
is a translate of `y`. The restricted `Gm`-action fixes `y` on every relative
scheme test and after every refinement of the test. The output also retains
an actual solvable closed subgroup `iS : S → G`, its exact all-test stabilizer
criterion, and a factorization `χS ≫ iS = χ`. Rational transitivity and
scheme-theoretic stabilizer membership are separate fields; the latter is
not inferred only from rational-point membership.

The proof first uses `affineLinearEmbeddingStatement` to embed `G` as a closed
subgroup of `GL_N`. The published `generalLinearSolvableStabilizer` gives a
proper nonempty general-linear scheme whose closed point stabilizers are
solvable. Its construction uses a stable locus in a Grassmannian which
corresponds to full flags over fields. The proof uses this existing witness
and does not identify it with the usual flag scheme on arbitrary rings.
The theorem `closedOrbit` constructs a reduced closed `G`-orbit in that
witness, including its action and rational transitivity. Closedness makes this
orbit proper.

The auxiliary theorem `SchemeAction.exists_isFixed_of_gm_of_isProper` works
over every field when a rational point is supplied. Properness implies
pseudo-completeness by `isPseudoComplete_of_isProper`. The orbit morphism of
the supplied rational point is equivariant for multiplication on `Gm`, so
`OrbitLimit.exists_isFixed_of_gm` produces an all-test fixed rational point.
This applies to the restricted cocharacter action on the proper closed orbit.
It uses the published elementary orbit-limit argument, rather than the
general solvable fixed-point theorem.

The all-test stabilizer of this fixed point is a closed subgroup by
`SchemeAction.exists_isClosedSubgroup_stabilizer`. Its composite with the
closed linear embedding fixes the corresponding point in the general-linear
witness, and hence is solvable by the witness's stabilizer theorem. Fixedness
puts the cocharacter's whole range functor inside this stabilizer.
Evaluating this range containment on the universal point of `Gm` gives a
factorization of the underlying morphism. Cancellation of the monomorphism
`iS` verifies its identity and multiplication laws, so it is an actual
group-scheme factorization. This does not require the cocharacter to be
injective. Finally, translating between the original closed-orbit base point
and the new fixed point preserves rational transitivity.

The construction invokes neither a Borel subgroup theorem nor a rank-one
root theorem. It leaves open any compatibility between the chosen fixed
point and the ordering of the cocharacter weights, and consequently does
not establish that this stabilizer lies in `Dynamic.parabolic χ`.
