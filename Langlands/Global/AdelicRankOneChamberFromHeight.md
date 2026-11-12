# Actual rank-one chamber reduction from an arithmetic height bound

This derived module connects an explicit arithmetic height input and actual positive
norm coordinates to the complete chamber factorization for a prescribed Iwasawa
compact subgroup in relative rank one. The input assertions remain premises; this
module does not prove either the general arithmetic bound or the positive coordinate
theorem, and it does not close the general chamber-reduction target.

`HasBoundedMinimalParabolicEigenline` asks for one finite-coordinate actual
representation whose exact selected-line stabilizer, on all scheme tests with unit
scalars, is the empty-index standard parabolic, and whose selected-vector height has
a positive uniform rational-orbit bound on ambient norm-one adelic points. The
published universal rank-one arithmetic statement implies this existential input:
the actual Chevalley construction supplies the representation and its exact
stabilizer, and the supplied arithmetic assertion bounds that representation.

The inverse ordered-product identity removes the actual unipotent and intrinsic
norm-one factors from the selected-vector height of `(u m s)⁻¹`. Its order is
`s⁻¹ m⁻¹ u⁻¹`: the unipotent coordinate-line stabilizer fixes the vector, so the
rightmost factor can be removed; right multiplication by the intrinsic norm-one
factor also preserves its height. No line-preservation premise on the torus is
needed for this identity. The remaining height is exactly the height at `s⁻¹`.

The compact-factor lemma uses the published uniform distortion bound for actual
primitive-vector heights. For a compact subgroup `K` there is a positive constant
`B` such that `H(p⁻¹) ≤ B H(k⁻¹ p⁻¹)` for all `k ∈ K`. Combining this with the
inverse identity shows that `H((u m s k)⁻¹) ≤ C` implies `H(s⁻¹) ≤ B C`,
uniformly in all four factors. The constant precedes all factor quantifiers.

The chamber theorem assumes actual connected reductive Siegel data with singleton
simple-relative-root set `{alpha}`, the bounded eigenline input, actual minimal
parabolic norm coordinates, and any specified subgroup `K` satisfying the existing
Iwasawa compact predicate. The proof first obtains the positive integral relation
between the eigenline character and `alpha` from the published actual rank-one
parabolic theorem. Exact line stabilization gives preservation on the canonical
unipotent and Levi sources; the Siegel setup makes the former unipotent.

For each ambient norm-one point `g`, the arithmetic input supplies a rational point
`q` with `H(g⁻¹ q) ≤ C`. Apply the given positive-coordinate Iwasawa factorization
to `q⁻¹ g`, obtaining the exact ordered product `u m a k`. Its inverse is exactly
`g⁻¹ q`, so the compact-factor estimate uniformly bounds the height on the inverse
of the torus image of `a`. This image lies in the ambient norm-one group by the
actual derived-torus clause of the Siegel setup. The positive integral root-character
relation and the published height-to-root comparison give a positive lower bound
on the root norm at `a`. Pullback along the actual torus map identifies this norm
with the one used by `weakSimpleRootChamber`. Since every simple root is `alpha`,
this is the entire chamber condition. The rational witness on the left is `q⁻¹`.

The conclusion is precisely `HasWeakChamberReduction` for the fixed data and the
original specified `K`, including the actual canonical factors, the intrinsic
norm-one Levi, the positive torus, the weak inequality and the exact product order.
The construction uses no splitness assumption on the ambient group and no compact
quotient or minimum-transport premise. Its provenance consists only of the
published actual Chevalley construction, line/root character relation, character
height identities, compact height-distortion estimate, positive-torus norm-one
containment and conditional positive-coordinate Iwasawa factorization.
