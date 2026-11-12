# Exact height scaling by an actual stabilized-line character

Author: Worker 83.

This derived module proves the exact scaling of an actual representation-vector
height under right translation by a subgroup preserving its coordinate line.
The factor is the normalized idelic norm of the actual algebraic line character.
Translation by the subgroup's actual norm-one points preserves the height.
The module also expresses the resulting height inequality as an equivalent
character-norm inequality.

## Actual affine action and character

Let `ρ` be a finite-coordinate representation of an actual group scheme over a
commutative base ring `R`, and let `j` be a coordinate index. Suppose
`ρ.PreservesCoordinateLine j`: every scheme-test point scales `e_j` by a
global unit. The published construction `coordinateLineCharacter` gives an
actual algebraic character with that scalar action.

`affine_coordinateLineCharacter_action` proves that, for every actual test
algebra `A` and point `x`, the matrix `ρ.affineMatrix A x` sends `e_j` to
`e_j` multiplied by
`Gm.affineUnitsEquiv R A (x ≫ coordinateLineCharacter)`. Thus the scalar is the
actual `A`-coefficient evaluation of the character, without an assumed
comparison between affine and global-section coordinates.

The proof uses `pointMatrix_eq_affineMatrix` and the canonical algebra
equivalence `Corepresented.affineSectionsAlgEquiv A` to compare the matrix
entries. The published identity `coordinateLineCharacter_scalar`, the
definition of `Gm.affineUnitsEquiv`, and the canonical section-isomorphism
comparison identify the character's affine value with the transported
global-section scalar. Applying the equivalence to each coordinate of the
published scalar-action equation proves the result.

## Heights and normalized character norms

Fix an arbitrary universe `u`, a number field `F : Type u`, an actual group
scheme `G` over `F`, and an actual representation
`ρ : G → GL_n`. The vector height is the published `orbitHeight`, using
the normalized coordinate height on actual primitive adelic vectors.

`orbitHeight_mul_eq_of_idele_scalar` takes a nonzero rational vector `v`,
two actual adelic points `g,h` and an idele `t`. If the actual adelic
representation matrix of `h` sends the principal vector `v` to `t · v`,
it proves

`orbitHeight(ρ,v,g h) = |t| · orbitHeight(ρ,v,g)`.

Here `|t|` is exactly `IdeleAbsoluteValue.full F t`, coerced to a real number.
The proof expands the representation's homomorphism law, composes the two
matrix actions and uses the specified scalar equation. Matrix multiplication
commutes with scalar multiplication. The vector at `g` is primitive by its
explicit invertible-matrix/nonzero-rational-vector presentation, so the
published `IsPrimitive.height_smul` gives the equality. Its normalization
includes the archimedean multiplicities.

For an actual group-scheme morphism `z : H → G` and an index `j : Fin n`,
suppose the restriction `ρ.restrict z` preserves the coordinate line.
No closedness, injectivity, reductivity or finite-type assumption is needed
for the following identities. Write `χ` for its actual
`coordinateLineCharacter`. The definition
`lineCharacterNorm F G H z ρ j hline` is the continuous multiplicative
map `characterNorm F H χ` from `H(𝔸_F)` to `ℝ≥0ˣ`. It is the norm of an
actual algebraic character, rather than a separately specified scalar map.

`orbitHeight_mul_map_eq_lineCharacterNorm` proves, for every `g ∈ G(𝔸_F)`
and `p ∈ H(𝔸_F)`,

`orbitHeight(ρ,e_j,g · map(z,p)) = |χ(p)| · orbitHeight(ρ,e_j,g)`.

The coordinate vector is nonzero by evaluation at `j`. Its principal adelic
vector is exactly the same coordinate vector over the adele ring. The affine
character-action theorem therefore supplies the scalar hypothesis of the
previous height theorem with `t = character F H χ p`.

`orbitHeight_mul_map_normOne` specializes to `p ∈ H(𝔸_F)¹`. By the
definition of the actual norm-one subgroup, the norm of every algebraic
character of `H`, including `χ`, is one. Substitution into the preceding
identity proves height invariance. The norm-one condition is on `H`;
membership of its image only in `G(𝔸_F)¹` is not asserted to suffice.

Finally, `orbitHeight_le_mul_map_iff` proves, for any real `c`,

`orbitHeight(ρ,e_j,g) ≤ c · orbitHeight(ρ,e_j,g · map(z,p))`
if and only if `1 ≤ c · |χ(p)|`.

It substitutes the exact scaling formula and cancels the strictly positive
height. No positivity assumption on `c` is necessary for this equivalence.

## Provenance and remaining obligations

This module is derived from the published actual coordinate-line character,
canonical affine section comparison, actual algebraic-character norm, and
normalized primitive-vector height-scaling theorems. Springer (1994),
§1.8(a), printed pp.209–210, is the source context for the height-scaling law.
The specialization to actual matrix representations and exact subgroup
character evaluation is implemented explicitly here.

The module assumes that the specified representation restricts to a preserved
line; it does not construct an adapted parabolic representation. Those choices
are provided separately by the actual Chevalley and closed-chain results.
It does not compare the line character to a simple relative root, establish a
uniform root bound, supply rank-one reduction, or prove
`AdelicSiegelChamberReductionStatement`.

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
Sci. (Math. Sci.) 104 (1994), 207–216. Registered source
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The cited original height passage was read directly.
