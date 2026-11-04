# Actual Haar balance on the common split-torus image

This internal deduction by Worker 184 combines the actual conjugation
determinant balance with the forward Haar formulas for the five subgroups
in that balance. It defines the full dynamic-unipotent Haar character and
proves the product, positive-half and inverse-half identities after pullback
along the displayed common split torus. There is no new literature claim.

## The full-subgroup character

`centralizingUnipotentHaarCharacter chi iZ hZ hUc` is the forward Haar
character for the action of the original `rationalPoints Z` on the literal
point subgroup `Dynamic.unipotent chi` in `G(k)`. Its normalizer-valued map
is `Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ`; its underlying
point is the original point followed by `iZ`. The character is the composite
of this map with `HaarModulus.closedNormalizerCharacter`.

This definition requires a topological field, affine `G`, the canonical
`pointTopology` on `G(k)`, local compactness, a topological-group structure,
all-test centralization of `chi` by the range of `iZ`, and closedness of the
literal point subgroup. It returns a monoid homomorphism into `ℝ≥0ˣ`.
The Haar convention is forward conjugation, \(x\mapsto zxz^{-1}\).
Neither a Lie-coordinate choice nor a supplied modulus identity is an
input to this definition.

## Balance hypotheses and conclusions

For the three balance theorems, `k` is a nonarchimedean local field with
its given valuation and topology, and `G` is smooth and affine. Let
`i : T.toGrp ⟶ G` have monomorphic underlying scheme map, let `hT` assert
that `T` is split, and let `hroot : HasRelativeRootSystem i`. The two
cocharacters are

\[
\chi=\operatorname{groupHom}(\zeta)\,;\,i,\qquad
\psi=\operatorname{groupHom}(\eta)\,;\,i.
\]

The affine group `Z` has a map `iZ : Z ⟶ G` whose range centralizes both
cocharacters on every test scheme. A displayed map `j : T.toGrp ⟶ Z`
satisfies `hj : j ≫ iZ = i`. The five affine groups `U,V,A,B,C`,
with their displayed inclusions into `G`, represent exactly

\[
U(\chi),\quad U(\psi),\quad
U(\chi)\cap Z_G(\psi),\quad U(\psi)\cap Z_G(\chi),\quad
U(\chi)\cap U(\psi),
\]

respectively. Each has finite Lie coordinates. These representability
and coordinate data remain explicit hypotheses. The canonical topology
on `G(k)` is assumed locally compact, Hausdorff and nonarchimedean as a
group; each of the five literal point subgroups is assumed closed.
No injectivity of `iZ` or `j` is required.

Write \(\delta_U,\delta_V\) for the newly defined full-subgroup
characters; \(\delta_A,\delta_B\) for the imported
`centralizingUnipotentCentralizerHaarCharacter` characters, with the
cocharacters ordered as above; and \(\delta_C\) for the imported
`centralizingUnipotentIntersectionHaarCharacter`. All five characters
have domain `rationalPoints Z` and use the same original acting point.
Set \(j_k=\operatorname{rationalPoints.map}(j)\).

`centralizingHaarCharacter_product_square_on_torus` proves equality of
monoid homomorphisms:

\[
(\delta_U\delta_V)\circ j_k
  =(\delta_A\delta_B\delta_C^2)\circ j_k.
\]

`centralizingHaarCharacter_positiveHalf_product_on_torus` uses the
canonical `Jacquet.positiveHalfCharacter` and proves

\[
(\delta_U^{1/2}\delta_V^{1/2})\circ j_k
  =(\delta_A^{1/2}\delta_B^{1/2}\delta_C)\circ j_k.
\]

Finally, write \(\iota\delta=\operatorname{Jacquet.complexCharacter}(\delta)\)
for the canonical embedding into complex units, and
\(\delta^{-1/2}=\operatorname{Jacquet.inverseHalfCharacter}(\delta)\)
for the inverse of the embedded canonical positive half.
`centralizingHaarCharacter_inverseHalf_product_on_torus` proves

\[
(\delta_U^{-1/2}\delta_V^{-1/2})\circ j_k
  =(\delta_A^{-1/2}\delta_B^{-1/2}(\iota\delta_C)^{-1})\circ j_k.
\]

Thus the intersection contributes its full modulus, with the inverse
in the inverse-half formula.

## Implemented proof and scope

The private commutation helper places the range of either cocharacter
in the dynamic centralizer of the other by factoring through the
commutative torus. For the first identity the proof evaluates at a torus
point and uses `Units.ext`. The full, positive/zero and positive/positive
Haar determinant theorems rewrite each factor as `distribHaarChar k`
applied to the determinant of its actual conjugation action. Multiplicativity
then reduces the result to
`Dynamic.rationalCharacterEval_centralizingDeterminant_product_square`.
The finite coordinates and represented groups are exactly those in that
determinant theorem.

Applying `Units.map NNReal.sqrtHom.toMonoidHom` to the first equality
and using `Jacquet.positiveHalfCharacter_sq` gives the second equality.
Applying the canonical map into complex units to the second equality
and taking inverses gives the third. These steps preserve the original
point map and the direction of the Haar factors.

All three identities are restricted along `j_k`. This file does not
deduce equality of characters on all of `Z(k)` from their agreement
on torus-image points. It proves no whole-common-Levi detection result,
normalized representation comparison, compact/full induction comparison,
ordered filtration or exact-\(K_0\) geometric expansion. Those are
separate remaining obligations of the host task; none is added as a
premise to its target.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
