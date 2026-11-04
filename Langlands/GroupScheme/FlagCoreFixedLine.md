# Stable lines of solvable groups from fixed points on projective space

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. The core's linear
algebra (`Langlands.GroupScheme.FlagCoreLinear`) needs a nonzero dual vector `w₀`
whose line is stable under a Borel subgroup `B`. This is the hypothesis
`FlagCore.StabilizesLine ρ.dual w₀ b` of `Langlands.GroupScheme.FlagCoreOrbits`. This
module derives it from the fixed-point theorem for smooth connected solvable groups
acting on proper schemes, `Langlands.GroupScheme.SolvableProperFixedPointStatement`.
That statement is a hypothesis of the two `FlagCore` theorems below; it is not proved
here. The fixed-point theorem is applied to the action of `B` on projective space
through the dual representation.

Notation. `R` is a commutative ring, `H` is a group scheme over `Spec R`, and
`ambient n R` is the projective space `ℙⁿ` over `Spec R`, an object of
`Over (Spec R)`. For a test point `x : Z ⟶ ambient n R`, `pointSection x` is the
corresponding section of `ℙⁿ_Z` over `Z.left`. For an invertible matrix `M` with entries
in `Γ(Z, ⊤)`, `matrixAction n M` is the automorphism of `ℙⁿ_Z` given by `M`. For
`v : m → k` and a test scheme `T` over `Spec k`, `v_T` denotes the vector
`(scalarMap T (v i))_i` with entries in `Γ(T, ⊤)`.

## The matrix action on projective space

These are in the namespace `Langlands.GroupScheme.ProjectiveOrbit`.

- `matrixActionHom σ`, for a matrix representation
  `σ : MatrixRepresentation H (Fin (n + 1))`: the morphism
  `H.X ⊗ ambient n R ⟶ ambient n R` over `Spec R` defined on the universal test point.
  It applies the matrix action of `σ` at the first projection to the section of the
  second projection, then maps `ℙⁿ_{H.X ⊗ ℙⁿ}` to `ℙⁿ`.
- `comp_matrixActionHom_left σ h x`: on a test `Z` with points `h` of `H` and `x` of
  `ℙⁿ`, the morphism `lift h x ≫ matrixActionHom σ` has underlying morphism
  `pointSection x ≫ matrixAction n (σ.pointMatrix Z h) ≫ map`. Proof: the Library
  naturality lemma `pointSection_matrixAction_naturality` applied to `lift h x`.
- `pointSection_eq_of_left y s hs hy`: a section `s` of `ℙⁿ_Z` whose image in `ℙⁿ` is
  `y.left` equals `pointSection y` (by `section_ext_of_map`).
- `matrixSchemeAction σ` (definition): the action `SchemeAction H (ambient n R)` with
  action morphism `matrixActionHom σ`, built by `schemeActionOfPointLaws`. The identity
  law holds since `σ` sends `1` to the identity matrix. The multiplication law holds
  since `σ` is multiplicative and `matrixAction` turns products into composites; the
  section of the intermediate point is identified by `pointSection_eq_of_left`.
- `matrixSchemeAction_act_left σ h x`: the underlying morphism of the action of `h` on
  `x` is `pointSection x ≫ matrixAction n (σ.pointMatrix Z h) ≫ map`.
- `isMatrixEquivariant_matrixSchemeAction σ`: the identity of `ℙⁿ` is matrix
  equivariant (`IsMatrixEquivariant`) for `matrixSchemeAction σ` and `σ`.

## Rational points and fixed points over a field

Here `k` is a field, and `ambient n (CommRingCat.of k)` is `ℙⁿ` over `Spec k`.

- `exists_pointSection_eq_basisSection x`: every rational point `x` of `ℙⁿ` over `k`
  is a coordinate section moved by a matrix. There are an index `j` and
  `P : GL (Fin (n + 1)) k` with `pointSection x` equal to the `j`-th basis section
  followed by `matrixAction n P` (entries of `P` mapped to global sections of
  `Spec k`). Proof: let `c` be the homogeneous coordinates of `x` from
  `ProjectiveSpace.pointCoordinates`, normalized so that `c j = 1`. Let `P` be the
  identity matrix with column `j` replaced by `c`; its determinant is `c j = 1`
  (`FlagCore.det_updateCol_one`), and `P e_j = c`. The point `P e_j` has homogeneous
  coordinates `c` (`hasCoordinates_fromOfGlobalSections` and `linearAction`). Two
  rational points lying on the same linear hyperplanes are equal
  (`ProjectiveSpace.eq_iff_linear_incidence`), which identifies the two points of
  `ProjectiveSpace k n`. `RelativeProjectiveSpace.hom_ext_toPolynomial` then identifies
  the two sections.
- `stabilizedLine_of_isFixed σ hx hP T h`: suppose a rational point `x` is fixed by
  `matrixSchemeAction σ` (`IsFixed`) and `pointSection x` is the basis section `j`
  moved by `P`, as above. Then on every test scheme `T` over `Spec k`, every point
  `h : T ⟶ H.X` satisfies `σ(h) v_T = a • v_T` for some unit `a` of `Γ(T, ⊤)`, where
  `v = P e_j`. Proof: pulled back to `T`, the section of `x` is the basis section `j`
  moved by `P_T`. Fixedness at `T` says that `σ(h) P_T` and `P_T` move the basis
  section to the same section. `translates_eq_iff` reduces this to `P_T⁻¹ σ(h) P_T`
  fixing the basis section, and `basisSection_matrixAction_eq_iff` gives
  `P_T⁻¹ σ(h) P_T e_j = a • e_j`. Multiplying by `P_T` gives the claim.

## Stable lines for solvable and Borel subgroups

These are in the namespace `Langlands.GroupScheme.FlagCore`; `k` is algebraically
closed.

- `exists_stabilizedLine hfix hconn hsolv σ`: let `H` be a group scheme over `Spec k`
  with `H.X.hom` smooth and affine, `H.X.left` connected, and `H` solvable. Assume
  `hfix : SolvableProperFixedPointStatement`. Then every matrix representation
  `σ : MatrixRepresentation H (Fin (n + 1))` has a nonzero `w : Fin (n + 1) → k` such
  that on every test `T`, every `h : T ⟶ H.X` satisfies `σ(h) w_T = a • w_T` for a
  unit `a` of `Γ(T, ⊤)`. Proof: `ℙⁿ` is proper and nonempty, so `hfix` gives a
  rational fixed point of `matrixSchemeAction σ`. Write it as `P e_j` by
  `exists_pointSection_eq_basisSection` and apply `stabilizedLine_of_isFixed`; the
  vector `P e_j` is nonzero because `P` is invertible.
- `exists_stabilizesLine_dual hfix hb ρ`: let `G` be a group scheme over `Spec k` with
  `G.X.hom` affine, let `b : B ⟶ G` be a Borel subgroup (`IsBorelSubgroup b`), and let
  `ρ : MatrixRepresentation G (Fin (n + 1))`. Assuming `hfix`, there is a nonzero
  `w₀` with `StabilizesLine ρ.dual w₀ b`. Proof: `B` is smooth, connected and
  solvable (fields of `IsBorelSubgroup`), and `B.X.hom` is affine because `b` is a
  closed immersion into the affine `G`. Apply `exists_stabilizedLine` to the
  restriction `ρ.dual.restrict b`. A point of `G` in the range of `b` is `y ≫ b` for
  a point `y` of `B`, and `MatrixRepresentation.pointMatrix_restrict` identifies the
  two point matrices.

## Provenance

These are internal helper results for the proof of task 877d0194. The matrix action
on projective space and the classification of rational points of projective space are
internal infrastructure; they do not come from a source.

The use of the dual line follows the proof of Milne, *Algebraic Groups* (2017),
Theorem 17.65 (printed pp. 374-375). There Milne takes a dual vector `v₀^∨` and a Borel
subgroup inside the stabilizer of its line. The route here differs. Since
`FlagCoreLinear` is formulated for a given Borel subgroup `B`, this module obtains a
`B`-stable dual line directly. It applies the fixed-point theorem for connected solvable
groups on complete varieties (Borel's fixed point theorem, which Milne cites as 17.3 in
the same proof) to `B` acting on `ℙ(V^∨)`. This is the usual proof of the Lie–Kolchin
theorem.
