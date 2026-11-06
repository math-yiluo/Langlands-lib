import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Additive root maps and rational generation for the binary special linear scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

section Matrices

variable {A B : Type u} [CommRing A] [CommRing B] {i j : Fin 2}

/-- A transvection is a homomorphism from the additive group of the coefficient ring. -/
def transvectionHom (hij : i ≠ j) : Multiplicative A →* Matrix.SpecialLinearGroup (Fin 2) A where
  toFun a := Matrix.SpecialLinearGroup.transvection hij a.toAdd
  map_one' := Matrix.SpecialLinearGroup.transvection_coeff_zero hij
  map_mul' a b := Matrix.SpecialLinearGroup.transvection_add hij a.toAdd b.toAdd

/-- Transvections commute with arbitrary changes of coefficient ring. -/
theorem map_transvection (f : A →+* B) (hij : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (f a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro r s
  simp [Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Matrix.one_apply, apply_ite f]

/-- Entrywise application of a ring equivalence gives an equivalence of special linear groups. -/
def matrixRingEquiv (e : A ≃+* B) :
    Matrix.SpecialLinearGroup (Fin 2) A ≃* Matrix.SpecialLinearGroup (Fin 2) B where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv a := by
    apply Matrix.SpecialLinearGroup.ext
    intro r s
    exact e.symm_apply_apply (a r s)
  right_inv a := by
    apply Matrix.SpecialLinearGroup.ext
    intro r s
    exact e.apply_symm_apply (a r s)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

end Matrices

section Schemes

variable (R : CommRingCat.{u}) {i j : Fin 2}

/-- The root map on every test scheme sends the sole additive coordinate to a transvection. -/
def rootPoints (hij : i ≠ j) (T : Over (Spec R)) :
    (T ⟶ (VectorGroup.groupScheme R 1).X) →*
      (T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) where
  toFun x := (SpecialLinear.pointsEquiv (Fin 2) R T).symm
    (Matrix.SpecialLinearGroup.transvection hij ((VectorGroup.coordinates R 1 T x).toAdd 0))
  map_one' := by
    apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
    rw [MulEquiv.apply_symm_apply, (VectorGroup.coordinates R 1 T).map_one,
      (SpecialLinear.pointsEquiv (Fin 2) R T).map_one]
    exact Matrix.SpecialLinearGroup.transvection_coeff_zero hij
  map_mul' x y := by
    apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
    simp only [MulEquiv.apply_symm_apply, map_mul]
    exact Matrix.SpecialLinearGroup.transvection_add hij _ _

/-- The transvection formula is natural on all relative test schemes. -/
theorem rootPoints_naturality (hij : i ≠ j) {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    rootPoints R hij T' (a ≫ x) = a ≫ rootPoints R hij T x := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R T').injective
  simp only [rootPoints, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.apply_symm_apply]
  change Matrix.SpecialLinearGroup.transvection hij
      ((VectorGroup.coordinates R 1 T' (a ≫ x)).toAdd 0) = _
  rw [SpecialLinear.pointsEquiv_naturality, MulEquiv.apply_symm_apply,
    map_transvection, VectorGroup.coordinates_comp]

/-- The actual additive root homomorphism into the binary special linear group scheme. -/
def rootMap (hij : i ≠ j) :
    VectorGroup.groupScheme R 1 ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  homOfPoints (rootPoints R hij) (rootPoints_naturality R hij)

/-- On every test scheme, the actual root homomorphism has the prescribed matrix formula. -/
theorem pointsEquiv_rootMap (hij : i ≠ j) (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (x ≫ (rootMap R hij).hom.hom) =
      Matrix.SpecialLinearGroup.transvection hij ((VectorGroup.coordinates R 1 T x).toAdd 0) := by
  rw [rootMap, comp_homOfPoints]
  exact (SpecialLinear.pointsEquiv (Fin 2) R T).apply_symm_apply _

/-- The upper additive root homomorphism. -/
abbrev upperMap : VectorGroup.groupScheme R 1 ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  rootMap R (show (0 : Fin 2) ≠ 1 by decide)

/-- The lower additive root homomorphism. -/
abbrev lowerMap : VectorGroup.groupScheme R 1 ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  rootMap R (show (1 : Fin 2) ≠ 0 by decide)

end Schemes

section RationalPoints

variable (k : Type u) [CommRing k]

/-- Actual rational points are determinant-one matrices over the base ring itself. -/
def rationalMatrixEquiv :
    rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k :=
  (SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k)
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).trans
      (matrixRingEquiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv)

/-- Each root-map image is the corresponding scalar transvection on rational points. -/
theorem rationalMatrixEquiv_rootMap {i j : Fin 2} (hij : i ≠ j)
    (x : rationalPoints (VectorGroup.groupScheme (CommRingCat.of k) 1)) :
    rationalMatrixEquiv k (rationalPoints.map (rootMap (CommRingCat.of k) hij) x) =
      Matrix.SpecialLinearGroup.transvection hij
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom
          ((VectorGroup.coordinates (CommRingCat.of k) 1 _ x).toAdd 0)) := by
  change Matrix.SpecialLinearGroup.map _
    (SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k) _
      (x ≫ (rootMap (CommRingCat.of k) hij).hom.hom)) = _
  rw [pointsEquiv_rootMap, map_transvection]
  rfl

/-- Every scalar transvection comes from a rational point of the actual additive root group. -/
theorem exists_rational_rootPoint {i j : Fin 2} (hij : i ≠ j) (a : k) :
    ∃ x : rationalPoints (VectorGroup.groupScheme (CommRingCat.of k) 1),
      rationalMatrixEquiv k (rationalPoints.map (rootMap (CommRingCat.of k) hij) x) =
        Matrix.SpecialLinearGroup.transvection hij a := by
  refine ⟨(VectorGroup.coordinates (CommRingCat.of k) 1 _).symm
    (Multiplicative.ofAdd fun _ => (Scheme.ΓSpecIso (CommRingCat.of k)).inv a), ?_⟩
  rw [rationalMatrixEquiv_rootMap, MulEquiv.apply_symm_apply]
  congr 1
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) a

end RationalPoints

section Generation

variable (k : Type u) [Field k]

/-- Any subgroup containing both additive root images contains every rational point of SL₂. -/
theorem eq_top_of_root_images
    (N : Subgroup (rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))))
    (hupper : (rationalPoints.map (upperMap (CommRingCat.of k))).range ≤ N)
    (hlower : (rationalPoints.map (lowerMap (CommRingCat.of k))).range ≤ N) : N = ⊤ := by
  apply top_unique
  intro x _
  let P : Matrix.SpecialLinearGroup (Fin 2) k → Prop :=
    fun a => (rationalMatrixEquiv k).symm a ∈ N
  have htrans : ∀ (i j : Fin 2) (hij : i ≠ j) a,
      P (Matrix.SpecialLinearGroup.transvection hij a) := by
    intro i j hij a
    obtain ⟨y, hy⟩ := exists_rational_rootPoint k hij a
    change (rationalMatrixEquiv k).symm _ ∈ N
    rw [← hy, MulEquiv.symm_apply_apply]
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hupper ⟨y, rfl⟩
    · exact hlower ⟨y, rfl⟩
    · exact (hij rfl).elim
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb
    change (rationalMatrixEquiv k).symm (a * b) ∈ N
    rw [map_mul]
    exact N.mul_mem ha hb
  have hx := Matrix.SL2.transvection_induction P htrans hmul (rationalMatrixEquiv k x)
  simpa only [P, MulEquiv.symm_apply_apply] using hx

/-- The two actual additive root images generate the entire rational-point group of SL₂. -/
theorem root_ranges_sup_eq_top :
    (rationalPoints.map (upperMap (CommRingCat.of k))).range ⊔
      (rationalPoints.map (lowerMap (CommRingCat.of k))).range = ⊤ :=
  eq_top_of_root_images k _ le_sup_left le_sup_right

end Generation

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
