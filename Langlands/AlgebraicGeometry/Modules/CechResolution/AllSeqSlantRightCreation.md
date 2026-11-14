# Right-axis creation and shuffle slant on actual cohomology

This internal extension of [AllSeqCreation](AllSeqCreation.md),
[AllSeqSlant](AllSeqSlant.md), and
[CechSlantRightCup](../../CechSlantRightCup.md) introduces no external theorem.
It transports the raw right-axis cup identity to ordered Čech homology and then
to actual right-derived structure-sheaf cohomology.

Let `R` be a commutative ring and let `P`, with projections `p₁` and `p₂`, be
the fibre product of schemes `X` and `Y` over `Spec R`. All three schemes have
section algebra structures agreeing with their structure maps. The index
families `U` and `V` are finite; twofold intersections of `U` and all nonempty
finite intersections of `V` are affine. The `R`-linear functional `l` on the
degree-one `U` cochains annihilates degree-zero coboundaries when slant is used
on homology. These hypotheses require no field or characteristic assumption.

`rightAxisCreationH n` is creation on the product-cover homology by the
pullback along `p₂` of a degree-one homology class on `Y`. The word right
specifies the geometric factor: the pulled-back class is still the left
argument of the ordered cup product.

`slantCochainMap_right_creation` identifies the composite of this cochain
creation with shuffle slant as the negative of creation after slant. Applying
the section/cochain equivalence reduces the equality to `L_cup_pull_right`,
with an arbitrary degree-`n+1` input cochain and a one-cocycle on `Y`.

`slantH_right_creationByCocycle` descends the equality using the short-complex
maps defining creation and slant. Homology preserves their compositions and
negatives. Two short-complex maps with equal middle components induce equal
homology maps, by the epimorphism from cycles and the monomorphism into
opcycles. This argument includes `n = 0`, where slant has degree-zero output;
it requires no surjective positive-degree cocycle presentation for that output.
Surjectivity of the degree-one class map then gives
`slantH_rightAxisCreationH` for every creating homology class.

For actual cohomology, also assume `Y` and `P` are separated over `Spec R`,
and `V` and the product family are affine open covers. The definition
`rightAxisCreationCanonical n` is actual creation on `P` after canonical
pullback of its creator from `Y`. This pullback is the actual
`relativeCohomologyPullback` followed by the pullback-unit comparison.

Writing `Sₙ : Hⁿ⁺¹(P, 𝒪) → Hⁿ(Y, 𝒪)` for the shuffle slant, the theorem
`slantCanonical_rightAxisCreationCanonical` proves, for every `n : ℕ`,
every `y ∈ H¹(Y, 𝒪)`, and every `e ∈ Hⁿ⁺¹(P, 𝒪)`,

\[
 S_{n+1}(p_2^*y\smile e)=-\,y\smile S_n(e).
\]

Its proof chooses preimages under the acyclic-resolution cohomology
equivalences. The established comparison of canonical pullback with the
ordered cochain map identifies the creating class; the homology identity and
linearity of the comparison equivalence then give the formula.

This contribution proves the right-axis identity in all degrees. The left-axis
identity, the full creation-contraction relation, and the host degree-two
exterior/coproduct comparison remain separate proof obligations.
