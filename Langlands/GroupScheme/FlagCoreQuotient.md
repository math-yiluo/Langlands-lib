# Proper Borel quotients and closed projective orbits for the flag covering core

Helper module for the covering core of
`Langlands.GroupScheme.FlagInvariantAffineOpenCoverStatement`. The core's linear
algebra (`Langlands.GroupScheme.FlagCoreLinear`) takes closed projective orbits as
hypotheses, in the form `FlagCore.IsClosedOrbit`. This module supplies the
geometric input for them: a proper quotient of `G` by a given Borel subgroup, and
the closed-orbit property for any vector whose line is stabilized by the fibers of
such a quotient.

Everything is in the namespace `Langlands.GroupScheme.FlagCore`. Here `k` is a
field and `G` is a group scheme over `Spec k`. "Rational points" are morphisms
`Over.mk (𝟙 (Spec k)) ⟶ G.X`.

## Definitions

Both definitions are propositions about a morphism `q : G.X ⟶ Q` over `Spec k`. They
name the two fiber conditions used below.

- `FibersInCosets q b`, for a subgroup `b : B ⟶ G`: the fibers of `q` lie in left
  cosets of `B`. On every test scheme `V`, if `V`-points `g, h` satisfy
  `g ≫ q = h ≫ q`, then `g⁻¹ * h` lies in `SubgroupFunctor.range b` at `V`.
- `FibersStabilizeLine σ v q`, for a matrix representation
  `σ : MatrixRepresentation G m` and a vector `v : m → k`: the fibers of `q`
  stabilize the line of `v`. On every test scheme `T`, if `T`-points `g, h`
  satisfy `g ≫ q = h ≫ q`, then the matrix `σ(g⁻¹ h)` maps the image
  `v_T = (scalarMap T (v i))_i` of `v` to `a • v_T` for some unit `a` of
  `Γ(T, ⊤)`.

## Small lemmas

- `comp_mulRight_hom x g`: right translation `GrpObj.mulRight x` by a rational
  point `x`, composed after a `V`-point `g`, is the product
  `g * G.constantPoint x V`. The proof unfolds `mulRight` and the multiplication
  of points.
- `ΓSpecIso_hom_scalarMap r`: over the base itself (`T = Over.mk (𝟙 (Spec k))`),
  `scalarMap T r` followed by `Γ(Spec k, ⊤) ≅ k` returns `r`. This is how matrices
  with entries `scalarMap T (M i l)` become the original matrix `M` again after
  `rationalMatrix` maps entries back to `k`.
- `det_updateCol_one v i`: replacing column `i` of the identity matrix by `v` gives
  a matrix with determinant `v i`. This is Cramer's rule for the identity
  (`cramer_apply`, `cramer_one`).

## A proper quotient by a given Borel subgroup

`exists_proper_quotient hproper hconj hb`, for `k` algebraically closed and `G`
smooth and affine over `k` with connected underlying space. It takes two upstream
statements as hypotheses:

- `hproper : SomeBorelQuotientProperStatement`: some Borel subgroup `b₀ : B₀ ⟶ G` has
  the property that every quotient with the listed properties is proper;
- `hconj : BorelConjugacyStatement`: any two Borel subgroups are conjugate by a
  rational point.

For every Borel subgroup `b : B ⟶ G` it gives `Q` over `Spec k` and `q : G.X ⟶ Q`
with `Q.hom` proper and `q.left` smooth, surjective and quasi-compact, and with
`FibersInCosets q b`: `g ≫ q = h ≫ q` implies `g⁻¹ * h ∈ range b` on every test
scheme `V`.

Proof. `smoothSubgroupQuotientExistence` gives the actual homogeneous quotient
`q₀ : G.X ⟶ Q` by `B₀`. Its fibers are exactly the left `B₀`-cosets, and `hproper`
then says `Q` is proper. `hconj` gives a rational point `x` and `φ : B₀ ≅ B` with
`b₀ ≫ int(x) = φ ≫ b`. Take `q := mulRight x ≫ q₀`. Right translation is an
isomorphism, so `q.left` is still smooth, surjective and quasi-compact. Write `c` for
the constant point of `x`. If `g ≫ q = h ≫ q`, then `(g c) ≫ q₀ = (h c) ≫ q₀`
(`comp_mulRight_hom`). So `(g c)⁻¹ (h c) = w ≫ b₀` for some `w`. Applying `int(x)`
(`comp_innerIso_hom`) and the conjugacy relation gives
`(w ≫ φ) ≫ b = c (c⁻¹ g⁻¹ h c) c⁻¹ = g⁻¹ h`.

## Closed orbits of lines with proper stabilizer quotients

`isClosedOrbit_of_isProper σ hv q hq`, for `k` algebraically closed and
`G.X.hom` locally of finite type. The data are:

- a matrix representation `σ : MatrixRepresentation G m` on a finite index type
  `m`;
- a nonzero vector `v : m → k`;
- `q : G.X ⟶ Q` with `q.left` flat, surjective and quasi-compact, and `Q.hom`
  proper;
- the hypothesis `hq : FibersStabilizeLine σ v q`: whenever `g ≫ q = h ≫ q` for
  `T`-points `g, h`, the matrix `σ(g⁻¹ h)` maps the image
  `v_T = (scalarMap T (v i))_i` of `v` to `a • v_T` for some unit `a` of
  `Γ(T, ⊤)`.

The conclusion is
`IsClosedOrbit (fun g => σ.rationalMatrix g *ᵥ v)`, indexed by the rational
points `g` of `G`. It says: every nonzero `c : m → k` on which every homogeneous
polynomial vanishing at all `σ(g) v` also vanishes is a nonzero multiple of some
`σ(g) v`.

Proof. The Library already has the special case of a coordinate line `e_j` of a
representation on `Fin (n + 1)`:
`ProjectiveOrbit.exists_eq_smul_orbit_of_isProper`. The proof reduces to it by a
change of coordinates.

1. Pick `i₀` with `v i₀ ≠ 0` and an equivalence `e : Fin (N + 1) ≃ m`. Let
   `A = updateCol 1 i₀ v`. Then `A` has `v` as column `i₀` and determinant
   `v i₀ ≠ 0` (`det_updateCol_one`), hence an inverse `A⁻¹`.
2. Let `Bm = A.submatrix id e` and `Cm = A⁻¹.submatrix e id`. Then
   `Cm * Bm = 1`, `Bm * Cm = 1` (`submatrix_mul_equiv`), and column `j₀ = e.symm i₀`
   of `Bm` is `v`.
3. Because `Bm * Cm = 1`, the stability condition `IsStableCoordinates σ Bm Cm`
   holds trivially. `MatrixRepresentation.restrictCoordinates` gives a representation
   `σ'` on `Fin (N + 1)` whose `T`-point matrices are
   `Cm_T * σ(g) * Bm_T` (entries mapped by `scalarMap T`).
4. In `σ'`, the fiber hypothesis `hq` for `v` becomes the corresponding hypothesis
   for the coordinate line `e_{j₀}`. Indeed `Bm_T e_{j₀} = v_T`, and `Cm_T Bm_T = 1`.
   So `exists_eq_smul_orbit_of_isProper` gives `IsClosedOrbit` for
   `g ↦ σ'(g) e_{j₀}`.
5. On rational points, `σ'(g) = Cm * σ(g) * Bm` (`ΓSpecIso_hom_scalarMap`). So
   `σ(g) v = A *ᵥ ((σ'(g) e_{j₀}) ∘ e.symm)`. Closedness transfers along
   `IsClosedOrbit.reindex` (by `e.symm`) and `IsClosedOrbit.mulVec` (by `A`).

## Provenance

These are internal helper results for the proof of task 877d0194. They follow the
geometric part of the proof of Milne, *Algebraic Groups* (2017), Theorem 17.65
(printed pp. 374-375). There `G/B` is complete, and so the orbit of a line with
stabilizer containing `B` is closed in projective space. Here completeness of
`G/B` comes from two upstream statements, which are hypotheses here:
`SomeBorelQuotientProperStatement` and `BorelConjugacyStatement` (the latter is
Milne, Theorem 17.9(b), per its Library docstring). The
closedness is stated on rational points by homogeneous equations, as
`IsClosedOrbit`. The definitions `FibersInCosets` and `FibersStabilizeLine` are
internal names for the two fiber conditions of this argument; they do not come
from the source.
