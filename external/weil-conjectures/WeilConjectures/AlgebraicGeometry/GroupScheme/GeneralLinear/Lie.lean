/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The Lie algebra of `GL_n` and rational representations

The infinitesimal points of the general linear group scheme `𝔾𝕃(n; k)` over a commutative ring `k`
are the invertible matrices `1 + εX` over the dual numbers `k[ε]`, with `X ∈ gl_n = Matrix n n k`;
their group law is `(1 + εX)(1 + εY) = 1 + ε(X + Y)`, and the mixed term of the commutator
`(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)` is the matrix commutator. Hence
`Lie(GL_n) = gl_n` with the commutator bracket.

A *rational representation* of a group scheme `G` over `k` on `k^m` is a homomorphism of group
schemes `r : G ⟶ GL_m`. Its differential `dr : Lie(G) → gl_m` is the differential of `r` read in
`gl_m` through `Lie(GL_m) = gl_m`; it is the `ε`-part of `r(1 + εx)`
(`AlgebraicGeometry.GeneralLinearGroup.RationalHom.differential_eq_map_snd`). The group–Lie
comparison for invariant subspaces, for connected group schemes locally of finite type over an
algebraically closed field of characteristic zero, is
`AlgebraicGeometry.GeneralLinearGroup.invariant_iff_differential_invariant`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.dualUnit`: the point `1 + εX` of `GL_n` over `k[ε]`.
- `AlgebraicGeometry.GeneralLinearGroup.toMatrix`: the matrix `X` of a tangent vector `1 + εX`.
- `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraEquivMatrix`: `Lie(GL_n) ≃ₗ⁅k⁆ gl_n`.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom`: rational representations `G ⟶ GL_m` of a
  group scheme `G` over `k`, with their action on points
  (`AlgebraicGeometry.GeneralLinearGroup.RationalHom.points`) and their differential
  (`AlgebraicGeometry.GeneralLinearGroup.RationalHom.differential`).

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.differential_eq_map_snd`: the differential of
  a rational representation on tangent points.
- `AlgebraicGeometry.GeneralLinearGroup.RationalHom.le_comap_toLin'_differential`: a subspace
  stable under the dual-number points of `G` is stable under the differential.
- `AlgebraicGeometry.GeneralLinearGroup.invariant_iff_differential_invariant`: a subspace is
  stable under a connected group scheme `G` if and only if it is stable under its differential.

## Implementation notes

The bracket on `Matrix n n k` is the commutator bracket `LieRing.ofAssociativeRing`, activated
locally as in `Mathlib.Algebra.Lie.Matrix`. Following `𝔾𝕃(n; k)`, the base ring is written `k`
even when it is only a commutative ring.

## Blueprint

- `def-wf-lie-algebra-derivation`: the Lie algebra of `GL_n` as its tangent space at the identity,
  rational representations and their differentials.
- `lemma-stable-subspaces-center`: subspaces stable under the group are stable under its Lie
algebra.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

section GeneralLinear

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

/-- The invertible matrix `1 + εX` over the dual numbers `k[ε]`, with inverse `1 - εX`: the point
of `GL_n` with values in `k[ε]` corresponding to the tangent vector `X ∈ gl_n`.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) : GL n (DualNumber k) :=
  ⟨1 + X.map inr, 1 - X.map inr,
    by rw [add_mul, one_mul, mul_sub, mul_one, Matrix.map_inr_mul_map_inr, sub_zero,
      sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, Matrix.map_inr_mul_map_inr, add_zero,
      add_sub_cancel_right]⟩

theorem coe_dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) : (dualUnit X : Matrix n n (DualNumber k)) = 1 + X.map inr :=
  rfl

/-- The matrix `1 + εX` reduces to the identity modulo `ε`. -/
@[simp]
theorem map_fstHom_dualUnit {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]
    (X : Matrix n n k) :
    Matrix.GeneralLinearGroup.map (fstHom k k k).toRingHom (dualUnit X) = 1 := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  change ((1 + X.map inr : Matrix n n (DualNumber k)) i j).fst = (1 : Matrix n n k) i j
  rw [Matrix.add_apply, fst_add, Matrix.map_apply, fst_inr, add_zero, Matrix.one_apply,
    Matrix.one_apply]
  split_ifs <;> rfl

end GeneralLinear

section Commutator

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

omit [DecidableEq n] in
/-- A square-zero scalar multiple of a matrix squares to zero. -/
theorem smul_mul_smul_eq_zero (e : R) (he : e * e = 0) (X : Matrix n n R) :
    (e • X) * (e • X) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, zero_smul]

/-- The commutator of `1 + eX` and `1 + dY` for `e² = d² = 0` is `1 + ed(XY - YX)`. -/
theorem one_add_smul_mul_one_add_smul_mul_one_sub_smul_mul_one_sub_smul (e d : R)
    (he : e * e = 0) (hd : d * d = 0) (X Y : Matrix n n R) :
    (1 + e • X) * (1 + d • Y) * (1 - e • X) * (1 - d • Y) = 1 + (e * d) • (X * Y - Y * X) := by
  set a := e • X
  set b := d • Y
  have haa : a * a = 0 := smul_mul_smul_eq_zero e he X
  have hbb : b * b = 0 := smul_mul_smul_eq_zero d hd Y
  have haba : a * b * a = 0 := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show e * (d * e) = e * e * d by ring, he, zero_mul, zero_smul]
  have hab : a * b = (e * d) • (X * Y) := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm d e]
  have hba : b * a = (e * d) • (Y * X) := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h₁ : (1 + a) * (1 + b) * (1 - a) = 1 + b + a * b - b * a - a * a - a * b * a := by
    noncomm_ring
  have h₂ : (1 + b + a * b - b * a) * (1 - b) =
      1 + a * b - b * a - b * b - a * (b * b) + b * a * b := by
    noncomm_ring
  have hbab : b * a * b = 0 := by
    simp only [a, b, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show d * (e * d) = d * d * e by ring, hd, zero_mul, zero_smul]
  rw [h₁, haa, haba, sub_zero, sub_zero, h₂, hbb, mul_zero, hbab, sub_zero, sub_zero, add_zero,
    add_sub_assoc, hab, hba, ← smul_sub]

end Commutator

section GeneralLinear

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [Field k]

/-- The matrix `X` of a tangent vector `1 + εX` of `GL_n`. -/
noncomputable def tangentMatrix (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) : Matrix n n k :=
  ((homMulEquiv n k (DualNumber k) p.1 : GL n (DualNumber k)) : Matrix n n (DualNumber k)).map
    snd

variable {n k}

theorem homMulEquiv_points_map {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (ψ : A →ₐ[k] B) (p : points 𝔾𝕃(n; k) A) :
    homMulEquiv n k B (points.map _ ψ p) =
      Matrix.GeneralLinearGroup.map ψ.toRingHom (homMulEquiv n k A p) :=
  homMulEquiv_specMap_comp ψ p

theorem coe_homMulEquiv_tangent (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    ((homMulEquiv n k (DualNumber k) p.1 : GL n (DualNumber k)) : Matrix n n (DualNumber k)) =
      1 + (tangentMatrix n k p).map inr := by
  refine Matrix.eq_one_add_map_inr_of_map_fst_eq_one ?_
  have h := homMulEquiv_points_map (n := n) (fstHom k k k) p.1
  rw [GrpObj.mem_pointsKer.1 p.2, map_one] at h
  exact (congrArg Units.val h).symm

theorem coe_homMulEquiv_tangentMap {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A]
    {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] (m : A) (hm : m * m = 0) (hπ : π m = 0)
    (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    ((homMulEquiv n k A (GrpObj.tangentMap m hm hπ p).1 : GL n A) : Matrix n n A) =
      1 + m • (tangentMatrix n k p).map (algebraMap k A) := by
  change ((homMulEquiv n k A (points.map _ _ p.1) : GL n A) : Matrix n n A) = _
  rw [homMulEquiv_points_map]
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_homMulEquiv_tangent]
  simp [Matrix.one_apply, apply_ite, DualNumber.liftElem_apply, mul_comm]

theorem tangentMatrix_injective : Function.Injective (tangentMatrix n k) := fun p q h ↦ by
  apply Subtype.ext
  apply (homMulEquiv n k (DualNumber k)).injective
  apply Units.ext
  rw [coe_homMulEquiv_tangent, coe_homMulEquiv_tangent, h]

theorem tangentMatrix_mul (p q : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    tangentMatrix n k (p * q) = tangentMatrix n k p + tangentMatrix n k q := by
  have hfst (r : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
      ((homMulEquiv n k (DualNumber k) r.1 : GL n (DualNumber k)) :
        Matrix n n (DualNumber k)).map fst = 1 := by
    rw [coe_homMulEquiv_tangent]
    ext i j
    simp [Matrix.one_apply, apply_ite]
  rw [tangentMatrix, Subgroup.coe_mul, map_mul, Units.val_mul,
    Matrix.map_snd_mul_of_map_fst_eq_one (hfst p) (hfst q)]
  rfl

theorem tangentMatrix_tangentScale (c : k) (p : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    tangentMatrix n k (GrpObj.tangentScale c p) = c • tangentMatrix n k p := by
  rw [tangentMatrix, GrpObj.tangentScale, coe_homMulEquiv_tangentMap]
  ext i j
  simp [Matrix.one_apply, apply_ite, algebraMap_eq_inl]

theorem coe_homMulEquiv_inv {A : Type u} [CommRing A] (g : GL n A) (N : Matrix n n A)
    (hN : N * N = 0) (hg : (g : Matrix n n A) = 1 + N) :
    ((g⁻¹ : GL n A) : Matrix n n A) = 1 - N := by
  have h : (g : Matrix n n A) * (1 - N) = 1 := by
    rw [hg, add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  calc ((g⁻¹ : GL n A) : Matrix n n A)
      = ((g⁻¹ : GL n A) : Matrix n n A) * ((g : Matrix n n A) * (1 - N)) := by rw [h, mul_one]
    _ = 1 - N := by rw [← mul_assoc, Units.inv_mul, one_mul]

open scoped commutatorElement in
/-- The commutator of two invertible matrices with square-zero scalar parts. -/
private theorem coe_commutator_of_eq_one_add_smul {A : Type u} [CommRing A] (e d : A)
    (he : e * e = 0) (hd : d * d = 0) (a b : GL n A) (X Y : Matrix n n A)
    (ha : (a : Matrix n n A) = 1 + e • X) (hb : (b : Matrix n n A) = 1 + d • Y) :
    (↑⁅a, b⁆ : Matrix n n A) = 1 + (e * d) • (X * Y - Y * X) := by
  have hai := coe_homMulEquiv_inv a _ (smul_mul_smul_eq_zero e he X) ha
  have hbi := coe_homMulEquiv_inv b _ (smul_mul_smul_eq_zero d hd Y) hb
  simp only [commutatorElement_def, Units.val_mul, ha, hb, hai, hbi]
  exact one_add_smul_mul_one_add_smul_mul_one_sub_smul_mul_one_sub_smul e d he hd X Y

open scoped commutatorElement in
/-- The matrix commutator of tangent points after two square-zero substitutions. -/
private theorem coe_homMulEquiv_tangentMap_commutator {A : Type u} [CommRing A] [Algebra k A]
    [IsLocalRing A] {π : A →ₐ[k] k} [IsLocalHom π.toRingHom] (e d : A)
    (he : e * e = 0) (hd : d * d = 0) (hπe : π e = 0) (hπd : π d = 0)
    (p q : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    ((homMulEquiv n k A
      (⁅GrpObj.tangentMap e he hπe p, GrpObj.tangentMap d hd hπd q⁆ :
        GrpObj.pointsKer 𝔾𝕃(n; k) π).1 : GL n A) : Matrix n n A) =
      1 + (e * d) •
        (tangentMatrix n k p * tangentMatrix n k q - tangentMatrix n k q * tangentMatrix n k p).map
          (algebraMap k A) := by
  let f : GrpObj.pointsKer 𝔾𝕃(n; k) π →* GL n A :=
    (homMulEquiv n k A).toMonoidHom.comp (GrpObj.pointsKer 𝔾𝕃(n; k) π).subtype
  change (↑(f ⁅GrpObj.tangentMap e he hπe p, GrpObj.tangentMap d hd hπd q⁆) : Matrix n n A) = _
  rw [map_commutatorElement]
  change (↑⁅homMulEquiv n k A (GrpObj.tangentMap e he hπe p).1,
    homMulEquiv n k A (GrpObj.tangentMap d hd hπd q).1⁆ : Matrix n n A) = _
  rw [coe_commutator_of_eq_one_add_smul e d he hd _ _ _ _
    (coe_homMulEquiv_tangentMap e he hπe p) (coe_homMulEquiv_tangentMap d hd hπd q)]
  simp only [← RingHom.mapMatrix_apply, map_sub, map_mul]

open scoped commutatorElement in
theorem tangentMatrix_tangentBracket (p q : GrpObj.pointsKer 𝔾𝕃(n; k) GrpObj.aug₁) :
    tangentMatrix n k (GrpObj.tangentBracket p q) =
      tangentMatrix n k p * tangentMatrix n k q - tangentMatrix n k q * tangentMatrix n k p := by
  have h := congrArg (fun r : GrpObj.pointsKer 𝔾𝕃(n; k) (GrpObj.aug₂ (k := k)) ↦
    ((homMulEquiv n k _ r.1 : GL n _) : Matrix n n (DualNumber (DualNumber k))))
    (GrpObj.tangentMul_tangentBracket p q)
  rw [GrpObj.tangentMul, coe_homMulEquiv_tangentMap,
    coe_homMulEquiv_tangentMap_commutator, add_right_inj] at h
  ext i j
  have hij := congrArg (fun M : Matrix n n (DualNumber (DualNumber k)) ↦ (M i j).snd.snd) h
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hij
  rwa [mul_comm, GrpObj.snd_snd_algebraMap₂_mul_eps₂_mul_del₂, mul_comm,
    GrpObj.snd_snd_algebraMap₂_mul_eps₂_mul_del₂] at hij

variable (n k)

/-- The matrix of a tangent vector of `GL_n`: the infinitesimal point `1 + εX` goes to `X`. -/
noncomputable def toMatrix (x : GrpObj.Lie 𝔾𝕃(n; k)) : Matrix n n k :=
  tangentMatrix n k (GrpObj.lieEquivTangent 𝔾𝕃(n; k) x)
/-- `Lie(GL_n) → gl_n` as a homomorphism of Lie algebras: the bracket is preserved because the
mixed term of the commutator `(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ(XY - YX)` is the matrix
commutator. -/
noncomputable def toMatrixLieHom : GrpObj.Lie 𝔾𝕃(n; k) →ₗ⁅k⁆ Matrix n n k where
  toFun := toMatrix n k
  map_add' x y := by
    rw [toMatrix, GrpObj.lieEquivTangent_add, tangentMatrix_mul]
    rfl
  map_smul' c x := by
    rw [toMatrix, GrpObj.lieEquivTangent_smul, tangentMatrix_tangentScale]
    rfl
  map_lie' {x y} := by
    rw [toMatrix, GrpObj.lieEquivTangent_lie, tangentMatrix_tangentBracket, Ring.lie_def]
    rfl

/-- `Lie(GL_n) → gl_n` is bijective: every infinitesimal point of `GL_n` is uniquely `1 + εX`. -/
theorem bijective_toMatrixLieHom : Function.Bijective (toMatrixLieHom n k) := by
  refine ⟨fun x y h ↦ (GrpObj.lieEquivTangent _).injective (tangentMatrix_injective h), fun X ↦ ?_⟩
  have hp : (homMulEquiv n k (DualNumber k)).symm (dualUnit X) ∈
      GrpObj.pointsKer 𝔾𝕃(n; k) (GrpObj.aug₁ (k := k)) := by
    rw [GrpObj.mem_pointsKer]
    apply (homMulEquiv n k k).injective
    rw [homMulEquiv_points_map, MulEquiv.apply_symm_apply, map_one]
    exact map_fstHom_dualUnit X
  refine ⟨(GrpObj.lieEquivTangent _).symm ⟨_, hp⟩, ?_⟩
  change tangentMatrix n k (GrpObj.lieEquivTangent _ ((GrpObj.lieEquivTangent _).symm _)) = X
  rw [Equiv.apply_symm_apply, tangentMatrix]
  simp only [MulEquiv.apply_symm_apply, coe_dualUnit]
  ext i j
  simp [Matrix.one_apply, apply_ite]

/-- The Lie algebra of the general linear group is `gl_n`, the matrices with the commutator
bracket: the tangent vector `1 + εX` corresponds to `X`.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def lieAlgebraEquivMatrix : GrpObj.Lie 𝔾𝕃(n; k) ≃ₗ⁅k⁆ Matrix n n k :=
  LieEquiv.ofBijective _ (bijective_toMatrixLieHom n k)

@[simp]
theorem lieAlgebraEquivMatrix_apply (x : GrpObj.Lie 𝔾𝕃(n; k)) :
    lieAlgebraEquivMatrix n k x = toMatrix n k x :=
  rfl

/-- The tangent vector of `GL_n` corresponding to the matrix `X` is the point `1 + εX`. -/
theorem infPointsEquivTangentGroup_lieAlgebraEquivMatrix_symm (X : Matrix n n k) :
    (GrpObj.infPointsEquivTangentGroup 𝔾𝕃(n; k)
      ((GrpObj.lieEquiv 𝔾𝕃(n; k)).symm ((lieAlgebraEquivMatrix n k).symm X)) :
        points 𝔾𝕃(n; k) (DualNumber k)) = (homMulEquiv n k (DualNumber k)).symm (dualUnit X) := by
  set x := (lieAlgebraEquivMatrix n k).symm X
  have hx : toMatrix n k x = X := (lieAlgebraEquivMatrix n k).apply_symm_apply X
  rw [MulEquiv.eq_symm_apply]
  apply Units.ext
  change ((homMulEquiv n k _ (GrpObj.lieEquivTangent _ x).1 : GL n (DualNumber k)) :
    Matrix n n (DualNumber k)) = _
  rw [coe_homMulEquiv_tangent, coe_dualUnit]
  exact congrArg (fun M : Matrix n n k ↦ 1 + M.map (inr : k → DualNumber k)) hx
end GeneralLinear

/-! ### Rational representations -/

section RationalHom

variable {k : Type u} [CommRing k] (G : Over (Spec (.of k))) [GrpObj G]
  (m : Type u) [Fintype m] [DecidableEq m]

/-- A rational representation of a group scheme `G` over `k` on `k^m`: a morphism of schemes
`G ⟶ GL_m` over `k`, required to be a homomorphism of group schemes through an `IsMonHom`
instance. (blueprint: `def-wf-lie-algebra-derivation`) -/
abbrev RationalHom :=
  G ⟶ 𝔾𝕃(m; k)

variable {G m}

namespace RationalHom

/-- A rational representation of `G` on `R`-points: the group homomorphism `G(R) → GL m R` given
by composing points `Spec R ⟶ G` with `r`. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def points (r : RationalHom G m) [IsMonHom r] (R : Type u) [CommRing R]
    [Algebra k R] : AlgebraicGeometry.points G R →* GL m R :=
  (homMulEquiv m k R).toMonoidHom.comp (IsMonHom.monoidHom r _)

theorem points_apply (r : RationalHom G m) [IsMonHom r] {R : Type u} [CommRing R] [Algebra k R]
    (g : AlgebraicGeometry.points G R) : r.points R g = homMulEquiv m k R (g ≫ r) :=
  rfl

/-- The entries of `r(g)` are the values at `g` of the functions `x_ij ∘ r` on `G`: the algebra
homomorphism `k[GL_m] → R` of the point `g ≫ r` applied to the coordinate functions. -/
theorem points_apply_apply (r : RationalHom G m) [IsMonHom r] {R : Type u} [CommRing R]
    [Algebra k R] (g : AlgebraicGeometry.points G R) (i j : m) :
    (r.points R g : Matrix m m R) i j =
      (Spec.mapMulEquiv.symm (g ≫ r) : WithConv (CoordinateRing m k →ₐ[k] R)).ofConv
        (coord m k i j) := by
  rw [points_apply, ← coe_genericUnit_apply]
  rfl

/-- The value at a point `g` of `G` of the function `c ∘ r`, for a function `c` on `GL_m`. -/
theorem appTop_appTop_ΓSpecIso_inv (r : RationalHom G m) [IsMonHom r] {R : Type u} [CommRing R]
    [Algebra k R] (g : AlgebraicGeometry.points G R) (c : CoordinateRing m k) :
    g.left.appTop (r.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing m k))).inv c)) =
      (Scheme.ΓSpecIso (.of R)).inv
        ((Spec.mapMulEquiv.symm (g ≫ r) : WithConv (CoordinateRing m k →ₐ[k] R)).ofConv c) := by
  have h := congr(($(Scheme.ΓSpecIso_inv_naturality (Spec.preimage (g ≫ r).left))).hom c)
  rw [Spec.map_preimage] at h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Over.comp_left, Scheme.Hom.comp_appTop] at h
  exact h.symm


variable (m) in
/-- The matrix coefficient `g ↦ l(g w)` of `GL_m`, for a linear form `l` and a vector `w` on
`k^m`, as a function on `GL_m`: `∑ᵢⱼ l(eᵢ) wⱼ xᵢⱼ`. -/
noncomputable def matrixCoefficient (l : Module.Dual k (m → k)) (w : m → k) :
    CoordinateRing m k :=
  ∑ i, ∑ j, (l (Pi.single i 1) * w j) • coord m k i j

/-- The value of a matrix coefficient at the point `g ≫ r` of `GL_m`. -/
theorem mapMulEquiv_symm_matrixCoefficient (r : RationalHom G m) [IsMonHom r] {R : Type u}
    [CommRing R] [Algebra k R] (g : AlgebraicGeometry.points G R) (l : Module.Dual k (m → k))
    (w : m → k) :
    (Spec.mapMulEquiv.symm (g ≫ r) : WithConv (CoordinateRing m k →ₐ[k] R)).ofConv
        (matrixCoefficient m l w) =
      ∑ i, ∑ j, algebraMap k R (l (Pi.single i 1) * w j) * (r.points R g : Matrix m m R) i j := by
  simp only [matrixCoefficient, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes,
    points_apply_apply]

theorem _root_.Module.Dual.apply_eq_sum_mul (l : Module.Dual k (m → k)) (w : m → k) :
    l w = ∑ i, w i * l (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ l w]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
/-- A rational representation commutes with base change of points along `R → S`. -/
theorem map_points (r : RationalHom G m) [IsMonHom r] {R S : Type u} [CommRing R] [Algebra k R]
    [CommRing S] [Algebra k S] (φ : R →ₐ[k] S) (g : AlgebraicGeometry.points G R) :
    Matrix.GeneralLinearGroup.map φ.toRingHom (r.points R g) =
      r.points S (AlgebraicGeometry.points.map G φ g) := by
  rw [points_apply, points_apply, AlgebraicGeometry.points.map, Category.assoc,
    homMulEquiv_specMap_comp]

end RationalHom

end RationalHom

section RationalHomField

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {m : Type u} [Fintype m] [DecidableEq m]

namespace RationalHom

/-- The differential `dr : Lie(G) → gl_m` of a rational representation `r`: the differential of
the homomorphism of group schemes `G ⟶ GL_m`, read in `gl_m` through `Lie(GL_m) = gl_m`. It is a
homomorphism of Lie algebras. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def differential (r : RationalHom G m) [IsMonHom r] :
    GrpObj.Lie G →ₗ⁅k⁆ Matrix m m k :=
  (lieAlgebraEquivMatrix m k).toLieHom.comp (GrpObj.differential r)

theorem differential_apply (r : RationalHom G m) [IsMonHom r] (x : GrpObj.Lie G) :
    r.differential x = lieAlgebraEquivMatrix m k (GrpObj.differential r x) :=
  rfl

/-- The matrix of a tangent vector `x` of `GL_m` is the `ε`-part of the matrix of its tangent
point. -/
theorem _root_.AlgebraicGeometry.GeneralLinearGroup.toMatrix_eq_map_snd
    (x : GrpObj.Lie 𝔾𝕃(m; k)) :
    toMatrix m k x =
      ((homMulEquiv m k (DualNumber k) (GrpObj.tangentPoint x) : GL m (DualNumber k)) :
        Matrix m m (DualNumber k)).map snd :=
  rfl

/-- The differential `dr(x)` of a rational representation `r` is the `ε`-part of the matrix
`r(1 + εx)`, the image under `r` of the tangent point of `x`. -/
theorem differential_eq_map_snd (r : RationalHom G m) [IsMonHom r] (x : GrpObj.Lie G) :
    r.differential x =
      ((r.points (DualNumber k) (GrpObj.tangentPoint x) : GL m (DualNumber k)) :
        Matrix m m (DualNumber k)).map snd := by
  rw [differential_apply, lieAlgebraEquivMatrix_apply, toMatrix_eq_map_snd,
    GrpObj.tangentPoint_differential, points_apply]

/-- `dr(X) v` is the `ε`-part of `r(1 + εX) v`, where `1 + εX` is the point of `G` over `k[ε]`
of the tangent vector `X`. -/
theorem toLin'_differential_apply (r : RationalHom G m) [IsMonHom r] (X : GrpObj.Lie G)
    (v : m → k) :
    Matrix.toLin' (r.differential X) v = snd ∘ ((r.points (DualNumber k)
      (GrpObj.infPointsEquivTangentGroup G ((GrpObj.lieEquiv G).symm X)) :
        Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) := by
  rw [differential_eq_map_snd]
  ext i
  simp [GrpObj.tangentPoint, Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum]

/-- If a subspace `U ⊆ k^m` is stable under the dual-number points of `G` acting by `r`, that is
the `ε`-part of `r(g) v` lies in `U` for `g ∈ G(k[ε])` and `v ∈ U`, then `U` is stable under the
differential of `r`: `dr(X) v` is the `ε`-part of `r(1 + εX) v`. -/
theorem le_comap_toLin'_differential (r : RationalHom G m) [IsMonHom r]
    (U : Submodule k (m → k))
    (hU : ∀ g : AlgebraicGeometry.points G (DualNumber k), ∀ v ∈ U,
      snd ∘ ((r.points (DualNumber k) g : Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) ∈ U)
    (X : GrpObj.Lie G) : U ≤ U.comap (Matrix.toLin' (r.differential X)) := by
  intro v hv
  have h := hU (GrpObj.lieEquivTangent G X).1 v hv
  rw [points_apply] at h
  have e := coe_homMulEquiv_tangent (GrpObj.kerPost r (GrpObj.lieEquivTangent G X))
  change ((homMulEquiv m k _ ((GrpObj.lieEquivTangent G X).1 ≫ r) : GL m (DualNumber k)) :
    Matrix m m (DualNumber k)) = _ at e
  rw [e] at h
  rw [Submodule.mem_comap, Matrix.toLin'_apply, differential_apply, lieAlgebraEquivMatrix_apply,
    toMatrix, GrpObj.lieEquivTangent_differential]
  convert h using 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply, apply_ite,
    TrivSqZeroExt.snd_sum]

end RationalHom

end RationalHomField

/-! ### The group–Lie comparison for invariant subspaces -/

section Comparison

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]
  {m : Type u} [Fintype m] [DecidableEq m]

namespace RationalHom

/-- For a reduced group scheme `G` locally of finite type over an algebraically closed field, a
subspace stable under `G(k)` is stable under the points of `G` with values in the dual numbers.

The condition `r(g) U ⊆ U` is cut out by the matrix coefficients `g ↦ l(r(g) w)`, `U ≤ ker l`,
`w ∈ U`, which are functions on `G`. They vanish at the `k`-points, so they vanish on the reduced
scheme `G` (`AlgebraicGeometry.eq_zero_of_forall_appTop_eq_zero`), and `r(g)` preserves
`U ⊗ k[ε]` for every `g ∈ G(k[ε])`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem snd_mulVec_mem_of_le_comap [IsAlgClosed k] [IsReduced G.left]
    [LocallyOfFiniteType G.hom] (r : RationalHom G m) [IsMonHom r] (U : Submodule k (m → k))
    (hU : ∀ g : AlgebraicGeometry.points G k, U ≤ U.comap (Matrix.toLin' (r.points k g)))
    (g : AlgebraicGeometry.points G (DualNumber k)) {v : m → k} (hv : v ∈ U) :
    snd ∘ ((r.points (DualNumber k) g : Matrix m m (DualNumber k)) *ᵥ (inl ∘ v)) ∈ U := by
  by_contra hw
  obtain ⟨l, hl, hUl⟩ := Submodule.exists_le_ker_of_notMem hw
  set e : m → m → k := fun i j ↦ if i = j then 1 else 0
  set c : CoordinateRing m k := ∑ i, ∑ j, (l (e i) * v j) • coord m k i j
  set a := r.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing m k))).inv c)
  have hc {R : Type u} [CommRing R] [Algebra k R] (g : AlgebraicGeometry.points G R) :
      (Spec.mapMulEquiv.symm (g ≫ r) : WithConv (CoordinateRing m k →ₐ[k] R)).ofConv c =
        ∑ i, ∑ j, algebraMap k R (l (e i) * v j) * (r.points R g : Matrix m m R) i j := by
    simp only [c, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, points_apply_apply]
  have hl' (w : m → k) : l w = ∑ i, w i * l (e i) := by
    rw [LinearMap.pi_apply_eq_sum_univ l w]
    simp [e, smul_eq_mul]
  have ha : a = 0 := by
    refine eq_zero_of_forall_appTop_eq_zero G.hom a fun p hp ↦ ?_
    let g : AlgebraicGeometry.points G k := Over.homMk p (by simpa [specOverSpec_over] using hp)
    have h := appTop_appTop_ΓSpecIso_inv r g c
    change p.appTop a = _ at h
    rw [h, hc, ← map_zero (Scheme.ΓSpecIso (.of k)).inv.hom]
    congr 1
    have h0 : l (Matrix.toLin' (r.points k g) v) = 0 := hUl (hU g hv)
    rw [hl', Matrix.toLin'_apply] at h0
    rw [← h0]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Algebra.algebraMap_self,
      RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h := appTop_appTop_ΓSpecIso_inv r g c
  rw [show r.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing m k))).inv c) = a from rfl, ha,
    map_zero, hc] at h
  have h1 := congrArg (Scheme.ΓSpecIso (.of (DualNumber k))).hom.hom h
  simp only [Iso.inv_hom_id_apply, map_zero] at h1
  have h0 := congrArg snd h1
  apply hl
  rw [hl']
  simp only [snd_zero, TrivSqZeroExt.snd_sum, Matrix.mulVec, dotProduct, Function.comp_apply]
    at h0 ⊢
  refine Eq.trans ?_ h0.symm
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp [TrivSqZeroExt.snd_mul, algebraMap_eq_inl]
  ring

/-- Over an algebraically closed field of characteristic zero, a subspace stable under the
differential of a rational representation of a connected group scheme `G` locally of finite type
is stable under `G(k)`.

It suffices that the matrix coefficients `f = l(r(·) w)`, `U ≤ ker l`, `w ∈ U`, vanish on `G`.
On an affine open `Spec A` around the identity `e`, the invariant derivation `D_X` of a tangent
vector `X` is the infinitesimal right translation by `1 + εX`
(`AlgebraicGeometry.GrpObj.exists_algHom_specMap_comp_eq_mul`), so
`D_X l(r(·) w) = l(r(·) dr(X) w)` and these functions form a set stable under all `D_X`, vanishing
at `e`. By Cartier's lemma (`AlgHom.mem_iInf_pow_ker_of_forall_exists_derivation`) they vanish
in the local ring at `e`, hence on the irreducible reduced scheme `G`.
(blueprint: `lemma-stable-subspaces-center`) -/
theorem le_comap_toLin'_points [IsAlgClosed k] [CharZero k] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] (r : RationalHom G m) [IsMonHom r] (U : Submodule k (m → k))
    (hU : ∀ X : GrpObj.Lie G, U ≤ U.comap (Matrix.toLin' (r.differential X)))
    (g : AlgebraicGeometry.points G k) : U ≤ U.comap (Matrix.toLin' (r.points k g)) := by
  classical
  have := GrpObj.isReduced_of_charZero G
  have := irreducibleSpace_of_connectedSpace G
  -- it suffices that the matrix coefficients `l(r(·) w)`, `U ≤ ker l`, `w ∈ U`, vanish on `G`
  suffices H : ∀ l : Module.Dual k (m → k), U ≤ LinearMap.ker l → ∀ w ∈ U,
      r.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing m k))).inv
        (matrixCoefficient m l w)) = 0 by
    intro w hw
    rw [Submodule.mem_comap]
    by_contra hgw
    obtain ⟨l, hl, hUl⟩ := Submodule.exists_le_ker_of_notMem hgw
    have h := appTop_appTop_ΓSpecIso_inv r g (matrixCoefficient m l w)
    rw [H l hUl w hw, map_zero, mapMulEquiv_symm_matrixCoefficient] at h
    have h1 := congrArg (Scheme.ΓSpecIso (.of k)).hom.hom h
    simp only [Iso.inv_hom_id_apply, map_zero] at h1
    apply hl
    rw [Module.Dual.apply_eq_sum_mul, Matrix.toLin'_apply, h1]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Algebra.algebraMap_self,
      RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  intro l hUl w hw
  -- an affine open neighbourhood `j : Spec A ⟶ G` of the identity
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (GrpObj.onePoint G)) (⊤ : G.left.Opens).2
  set A := Γ(G.left, V)
  let j : Spec A ⟶ G.left := hV.fromSpec
  let : Algebra k A := (Spec.preimage (j ≫ G.hom)).hom.toAlgebra
  have hj : j ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
    (Spec.map_preimage (j ≫ G.hom)).symm
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [← hj]
    infer_instance
  have : Algebra.FiniteType k A := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at this
    exact RingHom.finiteType_algebraMap.1 this
  have := Algebra.FiniteType.isNoetherianRing k A
  let jO : AlgebraicGeometry.points G A := Over.homMk j (by simpa [specOverSpec_over] using hj)
  have : IsOpenImmersion jO.left := inferInstanceAs (IsOpenImmersion hV.fromSpec)
  -- the identity, as a `k`-point `e` of `A`
  have hrange : Set.range η[G].left ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    rw [hV.range_fromSpec]
    convert hxV
    exact congrArg η[G].left.base (Subsingleton.elim (α := PrimeSpectrum k) _ _)
  let eS : Spec (.of k) ⟶ Spec A := IsOpenImmersion.lift j η[G].left hrange
  have heS : eS ≫ j = η[G].left := IsOpenImmersion.lift_fac _ _ _
  have he' : CommRingCat.ofHom (algebraMap k A) ≫ Spec.preimage eS = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← hj, ← Category.assoc, heS, Over.w η[G], Spec.map_id]
    rfl
  let e : A →ₐ[k] k := { (Spec.preimage eS).hom with commutes' c := congr(($he').hom c) }
  have hSpec_e : Spec.map (CommRingCat.ofHom e.toRingHom) = eS := Spec.map_preimage eS
  have he1 : points.map G e jO = 1 := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ j =
      (CartesianMonoidalCategory.toUnit ((Spec (.of k)).asOver (Spec (.of k))) ≫ η[G]).left
    have hid : ((Spec (.of k)).asOver (Spec (.of k))).hom = 𝟙 _ := by
      simp only [OverClass.asOver_hom, specOverSpec_over,
        Algebra.algebraMap_self]
      exact Spec.map_id _
    rw [hSpec_e, heS, Over.comp_left, Over.toUnit_left]
    erw [hid, Category.id_comp]
  set M := r.points A jO
  have hM1 (i j : m) : e ((M : Matrix m m A) i j) = (1 : Matrix m m k) i j := by
    have h := map_points r e jO
    rw [he1, map_one] at h
    exact congrArg (fun B : GL m k ↦ (B : Matrix m m k) i j) h
  -- the matrix coefficients `l'(r(·) w')` restricted to `Spec A`
  let F (l' : Module.Dual k (m → k)) (w' : m → k) : A :=
    ∑ i, ∑ j, (l' (Pi.single i 1) * w' j) • (M : Matrix m m A) i j
  have hF0 (l' : Module.Dual k (m → k)) (hl' : U ≤ LinearMap.ker l') (w' : m → k) (hw' : w' ∈ U) :
      e (F l' w') = 0 := by
    have h : l' w' = 0 := hl' hw'
    rw [Module.Dual.apply_eq_sum_mul] at h
    simp only [F, map_sum, map_smul, hM1, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  -- the invariant derivation of a tangent vector `v` acts on the matrix coefficients through `dr`
  have hDer (v : AlgebraicGeometry.points G (DualNumber k)) (hv : v ∈ tangentGroup G) :
      ∃ ψ : A →ₐ[k] DualNumber A, ∃ hψ : (fstHom k A A).comp ψ = AlgHom.id k A,
        (∀ l' w', DualNumber.derivationOfSection ψ hψ (F l' w') = F l' (Matrix.toLin'
          (r.differential (GrpObj.lieEquiv G ((GrpObj.infPointsEquivTangentGroup G).symm
            ⟨v, hv⟩))) w')) ∧
        (Spec.map (CommRingCat.ofHom ψ.toRingHom)).asOver (Spec (.of k)) ≫ jO =
          ((Spec.map (CommRingCat.ofHom (inlAlgHom k A A).toRingHom)).asOver (Spec (.of k)) ≫
            jO) * ((Spec.map (CommRingCat.ofHom (DualNumber.mapAlgebraMap A).toRingHom)).asOver
              (Spec (.of k)) ≫ v) := by
    obtain ⟨ψ, hψ, hΦ⟩ := GrpObj.exists_algHom_specMap_comp_eq_mul jO v ((mem_tangentGroup G).1 hv)
    refine ⟨ψ, hψ, fun l' w' ↦ ?_, hΦ⟩
    set N := r.points (DualNumber k) v
    have hdr (i : m) : Matrix.toLin' (r.differential (GrpObj.lieEquiv G
        ((GrpObj.infPointsEquivTangentGroup G).symm ⟨v, hv⟩))) w' i = ∑ j, (N i j).snd * w' j := by
      rw [toLin'_differential_apply, Equiv.symm_apply_apply, MulEquiv.apply_symm_apply]
      simp [N, Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum]
    have hM (i j : m) : (ψ ((M : Matrix m m A) i j)).snd =
        ∑ l, (M : Matrix m m A) i l * algebraMap k A (N l j).snd := by
      have h := congrArg (fun z ↦ (r.points (DualNumber A) z : Matrix m m (DualNumber A)) i j) hΦ
      simp only [map_mul, Units.val_mul] at h
      rw [← points.map, ← points.map, ← points.map, ← map_points, ← map_points, ← map_points] at h
      change ψ ((M : Matrix m m A) i j) = _ at h
      rw [h, Matrix.mul_apply, TrivSqZeroExt.snd_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      change (inl ((M : Matrix m m A) i l) * DualNumber.mapAlgebraMap A (N l j)).snd = _
      simp [TrivSqZeroExt.snd_mul]
    let D := DualNumber.derivationOfSection ψ hψ
    have hDM (i j : m) : D ((M : Matrix m m A) i j) =
        ∑ l, (M : Matrix m m A) i l * algebraMap k A (N l j).snd :=
      (DualNumber.derivationOfSection_apply ψ hψ _).trans (hM i j)
    change D (F l' w') = _
    simp only [F, map_sum, Derivation.map_smul, hDM, hdr]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Finset.smul_sum, Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Algebra.smul_def, map_mul]
    ring
  -- by Cartier's lemma, the matrix coefficient vanishes near the identity
  have hSpecId : (Spec.map (CommRingCat.ofHom (AlgHom.id k (DualNumber k)).toRingHom)).asOver
      (Spec (.of k)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have hmem : F l w ∈ ⨅ i : ℕ, RingHom.ker e ^ i := by
    refine AlgHom.mem_iInf_pow_ker_of_forall_exists_derivation (ε := e)
      (W := {a | ∃ l', U ≤ LinearMap.ker l' ∧ ∃ w' ∈ U, a = F l' w'})
      (fun a ⟨l', hl', w', hw', ha⟩ ↦ ha ▸ hF0 l' hl' w' hw') (fun φ ↦ ?_) ⟨l, hUl, w, hw, rfl⟩
    let τ := e.toDualNumber φ
    let v : AlgebraicGeometry.points G (DualNumber k) :=
      (Spec.map (CommRingCat.ofHom τ.toRingHom)).asOver (Spec (.of k)) ≫ jO
    have hv : v ∈ tangentGroup G := by
      rw [mem_tangentGroup, points.map, ← Category.assoc, specMap_asOver_comp_specMap_asOver,
        show (fstHom k k k).comp τ = e from AlgHom.ext fun a ↦ AlgHom.fst_toDualNumber _ _]
      exact he1
    obtain ⟨ψ, hψ, hDF, hΦ⟩ := hDer v hv
    refine ⟨DualNumber.derivationOfSection ψ hψ, ?_, fun a ha ↦ ?_⟩
    · rintro _ ⟨l', hl', w', hw', rfl⟩
      exact ⟨l', hl', _, hU _ hw', hDF l' w'⟩
    have h := congrArg ((Spec.map (CommRingCat.ofHom (DualNumber.mapOfAlgHom e).toRingHom)).asOver
      (Spec (.of k)) ≫ ·) hΦ
    simp only [MonObj.comp_mul, ← Category.assoc, specMap_asOver_comp_specMap_asOver] at h
    rw [show (DualNumber.mapOfAlgHom e).comp (inlAlgHom k A A) = (inlAlgHom k k k).comp e from
        AlgHom.ext fun a ↦ by ext <;> simp,
      show (DualNumber.mapOfAlgHom e).comp (DualNumber.mapAlgebraMap A) = AlgHom.id k _ from
        AlgHom.ext fun a ↦ by ext <;> simp, hSpecId, Category.id_comp] at h
    have he2 : (Spec.map (CommRingCat.ofHom ((inlAlgHom k k k).comp e).toRingHom)).asOver
        (Spec (.of k)) ≫ jO = 1 := by
      rw [← specMap_asOver_comp_specMap_asOver, Category.assoc]
      exact (congrArg _ he1).trans (MonObj.comp_one _)
    rw [he2, one_mul] at h
    have h' := congrArg Over.Hom.left h
    simp only [Over.comp_left] at h'
    have h'' := Spec.map_injective ((cancel_mono jO.left).1 h')
    have h2 : DualNumber.mapOfAlgHom e (ψ a) = τ a := congr(($h'').hom a)
    rw [DualNumber.derivationOfSection_apply, ← DualNumber.snd_mapOfAlgHom, h2,
      AlgHom.snd_toDualNumber, AlgHom.cotangentDerivation_of_mem]
  obtain ⟨s, hs, hsF⟩ := AlgHom.mem_iInf_pow_ker_iff.1 hmem
  -- so it vanishes on a neighbourhood of the identity, hence on the irreducible reduced `G`
  have hjf : j.appTop (r.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing m k))).inv
      (matrixCoefficient m l w))) = (Scheme.ΓSpecIso A).inv (F l w) := by
    have h := appTop_appTop_ΓSpecIso_inv r jO (matrixCoefficient m l w)
    rw [mapMulEquiv_symm_matrixCoefficient] at h
    refine h.trans (congrArg _ ?_)
    simp only [F, Algebra.smul_def]
    rfl
  by_contra hf
  rw [← basicOpen_eq_bot_iff] at hf
  set s' := (Scheme.ΓSpecIso A).inv s
  have hz0 : eS (IsLocalRing.closedPoint k) ∈ (Spec A).basicOpen s' := by
    change IsLocalRing.closedPoint k ∈ eS ⁻¹ᵁ (Spec A).basicOpen s'
    rw [Scheme.preimage_basicOpen]
    change _ ∈ (Spec (.of k)).basicOpen (eS.appTop s')
    rw [Scheme.Hom.appTop_ΓSpecIso_inv]
    change _ ∈ (Spec (.of k)).basicOpen ((Scheme.ΓSpecIso _).inv (e s))
    rw [hs, map_one, Scheme.basicOpen_of_isUnit _ isUnit_one]
    trivial
  obtain ⟨_, ⟨z, hz, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (j.isOpenEmbedding.isOpenMap _ ((Spec A).basicOpen s').isOpen) (G.left.basicOpen _).isOpen
    ⟨_, _, hz0, rfl⟩ (not_not.1 ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).not.2 hf))
  have hz' : z ∈ (Spec A).basicOpen ((Scheme.ΓSpecIso A).inv (F l w)) := by
    rw [← hjf]
    change z ∈ j ⁻¹ᵁ G.left.basicOpen _ at hy
    rwa [Scheme.preimage_basicOpen] at hy
  have hz'' : z ∈ (Spec A).basicOpen (s' * (Scheme.ΓSpecIso A).inv (F l w)) := by
    rw [Scheme.basicOpen_mul]
    exact ⟨hz, hz'⟩
  rw [← map_mul, hsF, map_zero, Scheme.basicOpen_zero] at hz''
  exact hz''

/-- The group–Lie comparison for invariant subspaces: over an algebraically closed field of
characteristic zero, a subspace is stable under a connected group scheme locally of finite type
acting by a rational representation if and only if it is stable under the differential of the
representation. (blueprint: `lemma-stable-subspaces-center`, `lemma-stable-subspaces-center--1`) -/
theorem _root_.AlgebraicGeometry.GeneralLinearGroup.invariant_iff_differential_invariant
    [IsAlgClosed k] [CharZero k] [ConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] (r : RationalHom G m) [IsMonHom r] (U : Submodule k (m → k)) :
    (∀ g : AlgebraicGeometry.points G k, U ≤ U.comap (Matrix.toLin' (r.points k g))) ↔
      ∀ X : GrpObj.Lie G, U ≤ U.comap (Matrix.toLin' (r.differential X)) :=
  haveI := GrpObj.isReduced_of_charZero G
  ⟨fun h ↦ r.le_comap_toLin'_differential U fun g _ hv ↦ r.snd_mulVec_mem_of_le_comap U h g hv,
    fun h ↦ r.le_comap_toLin'_points U h⟩

end RationalHom

end Comparison

end AlgebraicGeometry.GeneralLinearGroup
