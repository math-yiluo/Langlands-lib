import Langlands.GroupScheme.Reductive.GeneralLinearDiagonal

/-! # Permutation matrices normalize the diagonal torus of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Permutation matrices -/

section PermMatrix

variable (A : Type*) [CommRing A]

/-- The permutation matrix `P_w`, with `P_w e_b = e_{w b}`. -/
def permMatrix (w : Equiv.Perm n) : Matrix n n A :=
  Matrix.of fun a b => if a = w b then 1 else 0

theorem permMatrix_mul (w v : Equiv.Perm n) :
    permMatrix A w * permMatrix A v = permMatrix A (w * v) := by
  ext a b
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Equiv.Perm.mul_apply, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_eq_single (v b)]
  · simp only [ite_true]
    exact if_congr Iff.rfl rfl rfl
  · intro c _ hc
    simp [hc]
  · simp

omit [Fintype n] in
theorem permMatrix_one : permMatrix A (1 : Equiv.Perm n) = 1 := by
  ext a b
  simp only [permMatrix, Matrix.of_apply, Equiv.Perm.coe_one, id_eq, Matrix.one_apply]
  exact if_congr Iff.rfl rfl rfl

/-- The permutation matrix as an invertible matrix. -/
def permGL (w : Equiv.Perm n) : GL n A where
  val := permMatrix A w
  inv := permMatrix A w⁻¹
  val_inv := by rw [permMatrix_mul, mul_inv_cancel, permMatrix_one]
  inv_val := by rw [permMatrix_mul, inv_mul_cancel, permMatrix_one]

theorem coe_permGL (w : Equiv.Perm n) : (permGL A w : Matrix n n A) = permMatrix A w := rfl

variable {A} in
theorem map_permGL {B : Type*} [CommRing B] (f : A →+* B) (w : Equiv.Perm n) :
    Matrix.GeneralLinearGroup.map f (permGL A w) = permGL B w := by
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, coe_permGL, permMatrix, Matrix.of_apply]
  split_ifs
  · exact map_one f
  · exact map_zero f

/-- Permuting the coordinates of a family indexed by `ULift n`: `t ↦ (c ↦ t (w⁻¹ c))`. -/
def permuteCoords (M : Type*) [Monoid M] (w : Equiv.Perm n) :
    (ULift.{u} n → M) ≃* (ULift.{u} n → M) where
  toFun t c := t ⟨w⁻¹ c.down⟩
  invFun t c := t ⟨w c.down⟩
  left_inv t := by
    funext c
    simp
  right_inv t := by
    funext c
    simp
  map_mul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
theorem permuteCoords_apply (M : Type*) [Monoid M] (w : Equiv.Perm n) (t : ULift.{u} n → M)
    (c : ULift.{u} n) : permuteCoords M w t c = t ⟨w⁻¹ c.down⟩ := rfl

omit [Fintype n] [DecidableEq n] in
theorem permuteCoords_symm_apply (M : Type*) [Monoid M] (w : Equiv.Perm n)
    (t : ULift.{u} n → M) (c : ULift.{u} n) :
    (permuteCoords M w).symm t c = t ⟨w c.down⟩ := rfl

/-- Conjugating a diagonal matrix by a permutation matrix permutes the diagonal entries. -/
theorem permGL_mul_diagonalTorusUnits (w : Equiv.Perm n) (t : ULift.{u} n → Aˣ) :
    permGL A w * diagonalTorusUnits n A t =
      diagonalTorusUnits n A (permuteCoords Aˣ w t) * permGL A w := by
  ext a b
  simp only [Units.val_mul, coe_permGL, coe_diagonalTorusUnits, Matrix.mul_diagonal,
    Matrix.diagonal_mul, permMatrix, Matrix.of_apply, permuteCoords_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem permGL_conj_diagonalTorusUnits (w : Equiv.Perm n) (t : ULift.{u} n → Aˣ) :
    permGL A w * diagonalTorusUnits n A t * (permGL A w)⁻¹ =
      diagonalTorusUnits n A (permuteCoords Aˣ w t) := by
  rw [permGL_mul_diagonalTorusUnits, mul_inv_cancel_right]

end PermMatrix

/-! ### The permutation automorphisms of the diagonal torus -/

section TorusAut

variable (R : CommRingCat.{u})

local notation "𝔻" => splitTorus.commGroupScheme (Spec R) (ULift n)

/-- The permutation of coordinates on the points of the split torus over a test scheme. -/
def torusPermPoints (w : Equiv.Perm n) (U : Over (Spec R)) :
    (U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) ≃* (U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :=
  (splitTorus.pointsEquiv (ULift.{u} n) U).trans
    ((permuteCoords _ w).trans (splitTorus.pointsEquiv (ULift.{u} n) U).symm)

omit [DecidableEq n] in
theorem pointsEquiv_torusPermPoints (w : Equiv.Perm n) {U : Over (Spec R)}
    (x : U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    splitTorus.pointsEquiv (ULift.{u} n) U (torusPermPoints R w U x) =
      permuteCoords _ w (splitTorus.pointsEquiv (ULift.{u} n) U x) :=
  MulEquiv.apply_symm_apply _ _

omit [DecidableEq n] in
theorem torusPermPoints_naturality (w : Equiv.Perm n) {U U' : Over (Spec R)} (a : U' ⟶ U)
    (x : U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    torusPermPoints R w U' (a ≫ x) = a ≫ torusPermPoints R w U x := by
  apply (splitTorus.pointsEquiv (ULift.{u} n) U').injective
  rw [pointsEquiv_torusPermPoints, splitTorus.pointsEquiv_naturality,
    splitTorus.pointsEquiv_naturality, pointsEquiv_torusPermPoints]
  rfl

/-- The automorphism of the diagonal torus permuting the coordinates by `w`:
`(tᵢ) ↦ (t_{w⁻¹ i})`. -/
def torusPerm (w : Equiv.Perm n) : 𝔻 ≅ 𝔻 where
  hom := Additive.ofMul (isoOfPoints (torusPermPoints R w)
    (fun {_ _} a x => torusPermPoints_naturality R w a x)).hom
  inv := Additive.ofMul (isoOfPoints (torusPermPoints R w)
    (fun {_ _} a x => torusPermPoints_naturality R w a x)).inv
  hom_inv_id := congrArg Additive.ofMul (Iso.hom_inv_id _)
  inv_hom_id := congrArg Additive.ofMul (Iso.inv_hom_id _)

omit [DecidableEq n] in
theorem pointsEquiv_comp_torusPerm_hom (w : Equiv.Perm n) {U : Over (Spec R)}
    (x : U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    splitTorus.pointsEquiv (ULift.{u} n) U
        (x ≫ (CommGroupScheme.groupHom (torusPerm R w).hom).hom.hom) =
      permuteCoords _ w (splitTorus.pointsEquiv (ULift.{u} n) U x) := by
  rw [← pointsEquiv_torusPermPoints]
  exact congrArg _ (comp_isoOfPoints_hom (torusPermPoints R w)
    (fun {_ _} a x => torusPermPoints_naturality R w a x) U x)

omit [DecidableEq n] in
theorem pointsEquiv_comp_torusPerm_inv (w : Equiv.Perm n) {U : Over (Spec R)}
    (x : U ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    splitTorus.pointsEquiv (ULift.{u} n) U
        (x ≫ (CommGroupScheme.groupHom (torusPerm R w).inv).hom.hom) =
      (permuteCoords _ w).symm (splitTorus.pointsEquiv (ULift.{u} n) U x) := by
  have h := comp_isoOfPoints_inv (torusPermPoints R w)
    (fun {_ _} a x => torusPermPoints_naturality R w a x) U x
  refine (congrArg (splitTorus.pointsEquiv (ULift.{u} n) U) h).trans ?_
  change splitTorus.pointsEquiv (ULift.{u} n) U ((splitTorus.pointsEquiv (ULift.{u} n) U).symm
    ((permuteCoords _ w).symm (splitTorus.pointsEquiv (ULift.{u} n) U x))) = _
  exact MulEquiv.apply_symm_apply _ _

/-- The coordinate cocharacters are permuted by the inverse permutation automorphism. -/
theorem single_comp_torusPerm_inv (w : Equiv.Perm n) (c : ULift.{u} n) :
    splitTorus.single (Spec R) (ULift.{u} n) c ≫ (torusPerm R w).inv =
      splitTorus.single (Spec R) (ULift.{u} n) ⟨w⁻¹ c.down⟩ := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (splitTorus.pointsEquiv (ULift.{u} n) U).injective
  rw [comp_groupHom_comp, pointsEquiv_comp_torusPerm_inv, splitTorus.pointsEquiv_comp_single,
    splitTorus.pointsEquiv_comp_single]
  funext d
  rw [permuteCoords_symm_apply]
  by_cases hd : d = ⟨w⁻¹ c.down⟩
  · subst hd
    simp
  · have h2 : (⟨w d.down⟩ : ULift.{u} n) ≠ c := by
      intro h
      apply hd
      rw [← h]
      simp
    simp only [Pi.mulSingle_apply, hd, h2, ite_false]

end TorusAut

/-! ### Permutation base points -/

section PermPoint

variable (R : CommRingCat.{u})

/-- The base point of `GL_n` given by the permutation matrix of `w`. -/
def permPoint (w : Equiv.Perm n) : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme n R).X :=
  (pointsEquiv n R (Over.mk (𝟙 (Spec R)))).symm (permGL _ w)

theorem pointsEquiv_constantPoint (g : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme n R).X)
    (U : Over (Spec R)) :
    pointsEquiv n R U ((groupScheme n R).constantPoint g U) =
      Matrix.GeneralLinearGroup.map U.hom.appTop.hom
        (pointsEquiv n R (Over.mk (𝟙 (Spec R))) g) :=
  pointsEquiv_naturality _ g

theorem pointsEquiv_constantPoint_permPoint (w : Equiv.Perm n) (U : Over (Spec R)) :
    pointsEquiv n R U ((groupScheme n R).constantPoint (permPoint R w) U) = permGL _ w := by
  rw [pointsEquiv_constantPoint, permPoint, MulEquiv.apply_symm_apply]
  exact map_permGL _ w

/-- The permutation matrix of `w` normalizes the diagonal torus through `torusPerm w`. -/
theorem isNormalizingPoint_permPoint (w : Equiv.Perm n) :
    IsNormalizingPoint (diagonalTorus n R) (permPoint R w) (torusPerm R w) := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv n R U).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, Grp.comp_hom_hom,
    ← Category.assoc, map_mul, map_mul, map_inv, pointsEquiv_diagonalTorus,
    pointsEquiv_diagonalTorus, pointsEquiv_constantPoint_permPoint,
    permGL_conj_diagonalTorusUnits, pointsEquiv_comp_torusPerm_hom]

end PermPoint

/-! ### The Weyl action of permutation points -/

section WeylPerm

variable (k : Type u) [Field k]

/-- The permutation automorphism acts on characters by the permutation action. -/
theorem characterAut_torusPerm (w : Equiv.Perm n) :
    characterAut (torusPerm (CommRingCat.of k) w) = permutationAction n k w := by
  apply LinearEquiv.ext
  intro χ
  apply (characterCoordEquiv n k).injective
  funext c
  rw [characterCoordEquiv_permutationAction, characterAut_apply, characterCoordEquiv_apply,
    characterCoordEquiv_apply]
  change gmEndEquiv k (splitTorus.single _ _ ⟨c⟩ ≫ (torusPerm (CommRingCat.of k) w).inv ≫ χ) =
    gmEndEquiv k (splitTorus.single _ _ ⟨w⁻¹ c⟩ ≫ χ)
  rw [← Category.assoc, single_comp_torusPerm_inv]

/-- The permutation point as an element of the normalizer. -/
def permNormalizer (w : Equiv.Perm n) :
    normalizerPoints (diagonalTorus n (CommRingCat.of k)) :=
  ⟨permPoint _ w, ⟨torusPerm _ w, isNormalizingPoint_permPoint _ w⟩⟩

theorem weylAction_permNormalizer (w : Equiv.Perm n) :
    weylAction (diagonalTorus n (CommRingCat.of k)) (permNormalizer k w) =
      permutationAction n k w := by
  apply LinearEquiv.ext
  intro χ
  rw [weylAction_eq (n := permNormalizer k w) _ (isNormalizingPoint_permPoint _ w),
    ← characterAut_apply, characterAut_torusPerm]

theorem range_permutationAction_le_weylImage :
    (permutationAction n k).range ≤ weylImage (diagonalTorus n (CommRingCat.of k)) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨permNormalizer k w, weylAction_permNormalizer k w⟩

end WeylPerm

end Langlands.GroupScheme.GeneralLinear
