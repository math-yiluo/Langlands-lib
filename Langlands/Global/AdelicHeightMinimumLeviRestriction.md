# Restricting actual height minima through a fixed right factor

Author: Worker 83.

This derived prerequisite proves the representation identities used to restrict
successive height minima to a subgroup in Godement section 9.3, printed p.215
(PDF page 16). Its objects are the Library's actual group-scheme
representations, full number-field adelic points, principal rational maps and
primitive-vector heights. It does not prove the chamber-reduction theorem.

Godement writes a parabolic point as `p = z u`, where a unipotent group
containing `u` fixes the selected vectors and is normalized by the group
containing `z`. Removing `u` before and after right rational translation gives
the minimum inequalities in that smaller group. The Lean proves this
algebraic step under explicit fixing, normalization and subgroup-containment
hypotheses. It does not assume or construct the actual Levi data of the source.

## Fixedness and restriction

`IsOrbitVectorFixedBy F G ρ v N` is the proposition that every `x ∈ N`
fixes the principal image of the rational vector `v` under the actual adelic
matrix of `ρ`. Here `N` is a subgroup of `AdelicGroupPoints F G`, and `v`
is in `F^n`. This predicate imposes no nonzero-vector or positive-dimension
condition.

For any actual group-scheme morphism `f : H ⟶ G`,
`adelicMatrix_restrict` identifies the matrix of the restricted representation
on an adelic point of `H` with the matrix of its image in `G`.
`orbitHeight_restrict` consequently identifies their vector heights.
The proof uses the published affine-matrix restriction identity over the
actual adele algebra; no comparison with an unspecified matrix realization
is introduced.

`isOrbitVectorFixedBy_range_of_isFixedVector` evaluates the all-scheme-test
fixed-vector condition on the actual adele algebra. It concludes fixedness
on the range of the actual adelic map from a given group `U`.

`isOrbitVectorFixedBy_range_of_isUnipotent` supplies that condition for a
coordinate vector `e_j` when `U` is actually unipotent and the restriction
of `ρ` to `U` preserves the coordinate line on every scheme test.
The published `fixed_coordinateLine_of_isUnipotent` proves pointwise fixedness
of that line. The Lean identifies the scalar-map image of `e_j` with the same
coordinate vector over each test ring, and then applies the preceding
adelic-range result. No closedness or injectivity of `U ⟶ G` is required.

## Removing the right factor

Write `H_ρ,v(g)` for `orbitHeight F G ρ v g`.
For `x ∈ N`, `orbitHeight_mul_eq_of_fixed` proves

`H_ρ,v(g x) = H_ρ,v(g)`.

The proof expands the actual height and the representation's multiplicativity,
associates the matrix-vector action, and uses the fixed-vector equation.
This is an exact equality without a distortion constant.

If an adelic point `q` normalizes `N`,
`orbitHeight_mul_mul_eq_of_normalizer` proves

`H_ρ,v(g x q) = H_ρ,v(g q)`.

Indeed, `q⁻¹ x q ∈ N` and `g x q = (g q)(q⁻¹ x q)`.
The preceding equality removes this conjugate. Normalization is a genuine
hypothesis: fixedness of `x` on `v` alone would not justify this step.
Neither result requires `g`, `x` or `q` to be norm-one, and both allow a zero
vector.

## Transferring a finite family of minimum inequalities

`mem_chainHeightMinimalSet_restrict_of_fixed_factor` starts with the
published minimum set for an ambient family `ρ_i, v_i, Q_i`, with `i < r`
and constant `c`. It takes an actual morphism `f : H ⟶ G`, a rational
subgroup family `R_i` of `H`, and an index map `σ` carrying `i < s` into
`σ i < r`. Its additional premises are:

- `N` fixes `v_(σ i)` in each selected ambient representation.
- The rational image under `f` of every `q ∈ R_i` lies in `Q_(σ i)`.
- The principal adelic image of each such rational image normalizes `N`.
- The given ambient norm-one point `p` is `f(h) x`, for `x ∈ N` and a
  separately supplied point `h ∈ H(A)^1`.
- `p` belongs to the ambient minimum set.

The conclusion puts `h` in the minimum set for the restricted family
`ρ_(σ i)|_H, v_(σ i), R_i`, with the same constant `c`.
The proof tests the ambient inequality on the rational image of `q ∈ R_i`.
The two fixed-factor identities remove `x` on the left and its normalized
conjugate on the right. Naturality of the principal rational map and the
height restriction identity then give exactly the desired inequality in `H`.
No sign condition on `c`, subgroup nesting, or injectivity of `σ` is needed.
The empty target family is included.

`mem_chainHeightMinimalSet_restrict_of_unipotent_factor` specializes this
result to actual group-scheme maps `U ⟶ G` and `H ⟶ G`. It assumes
unipotence of `U`, all-test coordinate-line preservation in the selected
representations, and normalization of the adelic image of `U` by the
adelic image of `H`. The right factor is the actual image of an arbitrary
adelic point of `U`. Unipotence discharges all fixing premises, and
naturality puts every tested principal image in the adelic image of `H`,
discharging normalization. Rational comparison-subgroup containment and the
norm-one conditions remain explicit.

In particular, ambient `G(A)^1` membership is not used to infer `H(A)^1`
membership. The smaller group's character conditions must be established
separately when applying the theorem.

## Provenance and retained obligations

The source is R. Godement, *Domaines fondamentaux des groupes arithmétiques*,
Séminaire Bourbaki, Exposé 257 (1963; collected 1964), section 9.3,
printed p.215 (PDF page 16). Registered source:
`godement-1963-bourbaki-257-domaines-fondamentaux`, SHA-256
`b0a531469f376c1a56a7816f0fa579cd301c4162fb1c1aa8909c886e303c722d`.
The original rendered page was read directly. Its first paragraph removes
`U(1)` from the representation heights and restricts the rational comparison
groups to `Z(1)`. Its following paragraph applies the same method to the
rank-one group and its normalized unipotent complement.

The Lean generalizes this step to arbitrary number fields and universes,
arbitrary subgroup morphisms, chosen finite subfamilies and the Library's
normalized vector height. The source's structural assertions are retained
as explicit application obligations. The proof itself uses only published
affine representation comparisons, all-test unipotent fixedness and elementary
group identities, together with the existing definition of the minimum set.

This module does not prove the actual reductive Levi decompositions,
the normalization and rational-containment hypotheses for those Levi groups,
the smaller group's norm-one membership, the rank-one height-to-root bound,
the root-character comparison or the rank induction. None is an added
premise of a closing chamber theorem here. The full
`AdelicSiegelChamberReductionStatement` remains open.
