import Langlands.GroupScheme.BilinearCoordinateUnipotent
import Langlands.GroupScheme.BilinearCoordinateBaseChange
import Langlands.GroupScheme.KernelSquareTransport

/-! # Actual kernels of diagonal bilinear coordinate homomorphisms -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.BilinearCoordinate

private theorem kernelPoint_comp_eq_one {S : Scheme.{u}} {G H : GroupScheme S}
    (q : G ⟶ H) (T : Over S)
    (x : (((yonedaGrp.map q).app (op T)).hom.ker)) :
    x.val ≫ q.hom.hom = 1 :=
  x.property

section Algebra

variable {I : Type u} [Fintype I] {S : Type u} [CommRing S]

/-- The matrix multiplying each vector coordinate by its specified coefficient. -/
def diagonalMatrix (a : I → S) : I → I → S := fun i j => if i = j then a j else 0

@[simp]
theorem matrixVec_diagonalMatrix (a x : I → S) (j : I) :
    matrixVec (diagonalMatrix a) x j = a j * x j := by
  simp [matrixVec, diagonalMatrix, mul_ite, mul_comm]

omit [Fintype I] in
theorem map_diagonalMatrix {S' : Type u} [CommRing S'] (f : S →+* S') (a : I → S) :
    (fun i j => f (diagonalMatrix a i j)) = diagonalMatrix (fun i => f (a i)) := by
  funext i j
  simp [diagonalMatrix, apply_ite f]

/-- Extend the coordinates on a subset by zero. -/
def extendByZero (p : I → Prop) (a : {i // p i} → S) (i : I) : S :=
  if h : p i then a ⟨i, h⟩ else 0

omit [Fintype I] in
@[simp]
theorem extendByZero_apply (p : I → Prop) (a : {i // p i} → S) (i : {i // p i}) :
    extendByZero p a i = a i := by simp [extendByZero, i.property]

omit [Fintype I] in
theorem extendByZero_of_not (p : I → Prop) (a : {i // p i} → S) (i : I) (hi : ¬p i) :
    extendByZero p a i = 0 := by simp [extendByZero, hi]

private theorem sum_eq_subtype_of_zero (p : I → Prop) (f : I → S)
    (hf : ∀ i, ¬p i → f i = 0) :
    ∑ i, f i = ∑ i : {i // p i}, f i := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ i : {i // ¬p i}, f i = 0 :=
    Finset.sum_eq_zero (fun i _ => hf i i.property)
  rw [h0, add_zero]

/-- Restrict a bilinear law when both inputs vanish outside the chosen block. -/
theorem form_restrict (p : I → Prop) (c : I → I → S) (x y : I → S)
    (hx : ∀ i, ¬p i → x i = 0) (hy : ∀ i, ¬p i → y i = 0) :
    form c x y = form (fun (i j : {i // p i}) => c i j)
      (fun i => x i) (fun j => y j) := by
  unfold form
  rw [sum_eq_subtype_of_zero p _ (fun i hi => by simp [hx i hi])]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_eq_subtype_of_zero p _ (fun j hj => by simp [hy j hj])

end Algebra

section Maps

variable (R : CommRingCat.{u}) {I : Type u} [Fintype I]
  {c d : I → I → R} (a : I → R) (t : R) (h : IsCompatible c d (diagonalMatrix a) t)

/-- The actual diagonal coordinate homomorphism, with its cocycle compatibility. -/
abbrev diagonalHom : groupScheme R c ⟶ groupScheme R d :=
  linearHom R (diagonalMatrix a) t h

@[simp]
theorem pointsEquiv_diagonalHom_vec {T : Over (Spec R)} (x : T ⟶ (groupScheme R c).X)
    (i : I) :
    (pointsEquiv R d T (x ≫ (diagonalHom R a t h).hom.hom)).vec i =
      algebraMap R _ (a i) * (pointsEquiv R c T x).vec i := by
  rw [pointsEquiv_linearHom]
  change (∑ j, (pointsEquiv R c T x).vec j *
    algebraMap R _ (if j = i then a i else 0)) = _
  simp only [apply_ite (algebraMap R _), map_zero, mul_ite, mul_zero]
  simp [mul_comm]

@[simp]
theorem pointsEquiv_diagonalHom_scalar {T : Over (Spec R)} (x : T ⟶ (groupScheme R c).X) :
    (pointsEquiv R d T (x ≫ (diagonalHom R a t h).hom.hom)).scalar =
      algebraMap R _ t * (pointsEquiv R c T x).scalar := by
  rw [pointsEquiv_linearHom]
  rfl

end Maps

section Field

variable {k : Type u} [Field k] {I : Type u} [Fintype I]
  {c d : I → I → k} (a : I → k) (t : k)
  (h : IsCompatible c d (diagonalMatrix a) t)

/-- The scheme-theoretic kernel equations hold on all tests, including nonreduced ones. -/
theorem diagonalHom_eq_one_iff (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (groupScheme (CommRingCat.of k) c).X) :
    x ≫ (diagonalHom (CommRingCat.of k) a t h).hom.hom = 1 ↔
      (∀ i, a i ≠ 0 → (pointsEquiv (CommRingCat.of k) c T x).vec i = 0) ∧
        (t ≠ 0 → (pointsEquiv (CommRingCat.of k) c T x).scalar = 0) := by
  constructor
  · intro hx
    constructor
    · intro i hi
      have he := congrArg (fun y => (pointsEquiv (CommRingCat.of k) d T y).vec i) hx
      rw [pointsEquiv_diagonalHom_vec, map_one] at he
      exact (((isUnit_iff_ne_zero.mpr hi).map (algebraMap k _)).mul_right_eq_zero).mp he
    · intro ht
      have he := congrArg (fun y => (pointsEquiv (CommRingCat.of k) d T y).scalar) hx
      rw [pointsEquiv_diagonalHom_scalar, map_one] at he
      exact (((isUnit_iff_ne_zero.mpr ht).map (algebraMap k _)).mul_right_eq_zero).mp he
  · rintro ⟨hx, hb⟩
    apply (pointsEquiv (CommRingCat.of k) d T).injective
    apply Coordinates.ext
    · funext i
      rw [pointsEquiv_diagonalHom_vec, map_one]
      by_cases hi : a i = 0
      · simp [hi]
      · rw [hx i hi, mul_zero]
        rfl
    · rw [pointsEquiv_diagonalHom_scalar, map_one]
      by_cases ht : t = 0
      · simp [ht]
      · rw [hb ht, mul_zero]
        rfl

/-- The remaining vector indices of a diagonal kernel. -/
abbrev kernelIndices := {i : I // a i = 0}

/-- Restriction of the source cocycle to its surviving vector coordinates. -/
abbrev kernelCoefficients : kernelIndices a → kernelIndices a → k := fun i j => c i j

private theorem diagonalKernelPoint_vec (T : Over (Spec (CommRingCat.of k)))
    (x : (((yonedaGrp.map (diagonalHom (CommRingCat.of k) a t h)).app (op T)).hom.ker))
    (i : I) (hi : a i ≠ 0) :
    (pointsEquiv (CommRingCat.of k) c T x.val).vec i = 0 := by
  have hx := kernelPoint_comp_eq_one
    (diagonalHom (CommRingCat.of k) (c := c) (d := d) a t h) T x
  have he := congrArg (fun y => (pointsEquiv (CommRingCat.of k) d T y).vec i) hx
  rw [pointsEquiv_diagonalHom_vec, map_one] at he
  exact (((isUnit_iff_ne_zero.mpr hi).map (algebraMap k _)).mul_right_eq_zero).mp he

/-- If the scalar coefficient is zero, the actual kernel has a bilinear coordinate law. -/
def diagonalZeroKernelPointEquiv (ht : t = 0) (T : Over (Spec (CommRingCat.of k))) :
    (((yonedaGrp.map (diagonalHom (CommRingCat.of k) a t h)).app (op T)).hom.ker) ≃*
      Coordinates (algebraCoefficients (CommRingCat.of k) (kernelCoefficients (c := c) a)
        ((algΓ (CommRingCat.of k)).obj T).unop) where
  toFun x := ⟨fun i => (pointsEquiv (CommRingCat.of k) c T x.val).vec i,
    (pointsEquiv (CommRingCat.of k) c T x.val).scalar⟩
  invFun y := ⟨(pointsEquiv (CommRingCat.of k) c T).symm
    ⟨extendByZero (fun i => a i = 0) y.vec, y.scalar⟩, by
    change _ ≫ (diagonalHom (CommRingCat.of k) a t h).hom.hom = 1
    rw [diagonalHom_eq_one_iff, MulEquiv.apply_symm_apply]
    refine ⟨?_, fun hn => False.elim (hn ht)⟩
    intro i hi
    change extendByZero (fun i => a i = 0) y.vec i = 0
    exact extendByZero_of_not (fun i => a i = 0) y.vec i hi⟩
  left_inv x := by
    apply Subtype.ext
    apply (pointsEquiv (CommRingCat.of k) c T).injective
    rw [MulEquiv.apply_symm_apply]
    apply Coordinates.ext
    · funext i
      change extendByZero (fun i => a i = 0)
        (fun j => (pointsEquiv (CommRingCat.of k) c T x.val).vec j) i =
          (pointsEquiv (CommRingCat.of k) c T x.val).vec i
      by_cases hi : a i = 0
      · simp [extendByZero, hi]
      · simp only [extendByZero, dite_eq_right hi]
        exact (diagonalKernelPoint_vec a t h T x i hi).symm
    · rfl
  right_inv y := by
    change (⟨_, _⟩ : Coordinates _) = y
    simp only [MulEquiv.apply_symm_apply]
    apply Coordinates.ext
    · funext i
      exact extendByZero_apply _ _ i
    · rfl
  map_mul' x y := by
    change (⟨fun (i : kernelIndices a) =>
      (pointsEquiv (CommRingCat.of k) c T (x.val * y.val)).vec i,
      (pointsEquiv (CommRingCat.of k) c T (x.val * y.val)).scalar⟩ : Coordinates _) = _
    rw [map_mul]
    apply Coordinates.ext
    · rfl
    · change _ + _ + form _ _ _ = _ + _ + form _ _ _
      congr 1
      exact form_restrict (fun i => a i = 0) _ _ _
        (diagonalKernelPoint_vec a t h T x)
        (diagonalKernelPoint_vec a t h T y)

/-- Restricted bilinear coordinates on the actual zero-scalar kernel. -/
def diagonalZeroKernelCoordinates (ht : t = 0) (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) ≃*
      Coordinates (algebraCoefficients (CommRingCat.of k) (kernelCoefficients (c := c) a)
        ((algΓ (CommRingCat.of k)).obj T).unop) :=
  (kernelPointsEquiv (diagonalHom (CommRingCat.of k) a t h) T).trans
    (diagonalZeroKernelPointEquiv a t h ht T)

theorem diagonalZeroKernelCoordinates_naturality (ht : t = 0)
    {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T)
    (x : T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) :
    diagonalZeroKernelCoordinates a t h ht T' (f ≫ x) =
      (functor (CommRingCat.of k) (kernelCoefficients (c := c) a)).map
        ((algΓ (CommRingCat.of k)).map f).unop
        (diagonalZeroKernelCoordinates a t h ht T x) := by
  change (⟨fun (i : kernelIndices a) => (pointsEquiv (CommRingCat.of k) c T'
      ((f ≫ x) ≫ (kernelι (diagonalHom (CommRingCat.of k) a t h)).hom.hom)).vec i,
    (pointsEquiv (CommRingCat.of k) c T'
      ((f ≫ x) ≫ (kernelι (diagonalHom (CommRingCat.of k) a t h)).hom.hom)).scalar⟩ :
      Coordinates _) = _
  rw [Category.assoc, pointsEquiv_naturality]
  apply Coordinates.ext <;> rfl

private def diagonalZeroKernelTestEquiv (ht : t = 0)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) ≃*
      (T ⟶ (groupScheme (CommRingCat.of k) (kernelCoefficients (c := c) a)).X) :=
  (diagonalZeroKernelCoordinates a t h ht T).trans
    (pointsEquiv (CommRingCat.of k) (kernelCoefficients (c := c) a) T).symm

private theorem diagonalZeroKernelTestEquiv_naturality (ht : t = 0)
    {T T' : Over (Spec (CommRingCat.of k))} (f : T' ⟶ T)
    (x : T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) :
    diagonalZeroKernelTestEquiv a t h ht T' (f ≫ x) =
      f ≫ diagonalZeroKernelTestEquiv a t h ht T x := by
  apply (pointsEquiv (CommRingCat.of k) (kernelCoefficients (c := c) a) T').injective
  simp only [diagonalZeroKernelTestEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, pointsEquiv_naturality,
    diagonalZeroKernelCoordinates_naturality]

/-- When the scalar coefficient vanishes, the actual kernel is the restricted
bilinear group, over the original field. -/
def diagonalZeroKernelIso (ht : t = 0) :
    kernel (diagonalHom (CommRingCat.of k) a t h) ≅
      groupScheme (CommRingCat.of k) (kernelCoefficients (c := c) a) :=
  isoOfPoints (diagonalZeroKernelTestEquiv a t h ht)
    (diagonalZeroKernelTestEquiv_naturality a t h ht)

@[simp]
theorem pointsEquiv_diagonalZeroKernelIso_hom (ht : t = 0)
    (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) :
    pointsEquiv (CommRingCat.of k) (kernelCoefficients (c := c) a) T
        (x ≫ (diagonalZeroKernelIso a t h ht).hom.hom.hom) =
      diagonalZeroKernelCoordinates a t h ht T x := by
  rw [diagonalZeroKernelIso, comp_isoOfPoints_hom]
  exact (pointsEquiv (CommRingCat.of k) (kernelCoefficients (c := c) a) T).apply_symm_apply _

private theorem diagonalKernelPoint_scalar (ht : t ≠ 0)
    (T : Over (Spec (CommRingCat.of k)))
    (x : (((yonedaGrp.map (diagonalHom (CommRingCat.of k) a t h)).app (op T)).hom.ker)) :
    (pointsEquiv (CommRingCat.of k) c T x.val).scalar = 0 := by
  have hx := kernelPoint_comp_eq_one
    (diagonalHom (CommRingCat.of k) (c := c) (d := d) a t h) T x
  have he := congrArg (fun y => (pointsEquiv (CommRingCat.of k) d T y).scalar) hx
  rw [pointsEquiv_diagonalHom_scalar, map_one] at he
  exact (((isUnit_iff_ne_zero.mpr ht).map (algebraMap k _)).mul_right_eq_zero).mp he

/-- For nonzero scalar coefficient, the remaining vector coordinates are additive. -/
def diagonalNonzeroKernelPointEquiv (ht : t ≠ 0) {n : ℕ} (b : Fin n ≃ kernelIndices a)
    (T : Over (Spec (CommRingCat.of k))) :
    (((yonedaGrp.map (diagonalHom (CommRingCat.of k) a t h)).app (op T)).hom.ker) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) where
  toFun x := Multiplicative.ofAdd
    (fun i => (pointsEquiv (CommRingCat.of k) c T x.val).vec (b i))
  invFun y := ⟨(pointsEquiv (CommRingCat.of k) c T).symm
    ⟨extendByZero (fun i => a i = 0) (fun j => y.toAdd (b.symm j)), 0⟩, by
    change _ ≫ (diagonalHom (CommRingCat.of k) a t h).hom.hom = 1
    rw [diagonalHom_eq_one_iff, MulEquiv.apply_symm_apply]
    refine ⟨?_, fun _ => rfl⟩
    intro i hi
    change extendByZero (fun i => a i = 0) (fun j => y.toAdd (b.symm j)) i = 0
    exact extendByZero_of_not (fun i => a i = 0) (fun j => y.toAdd (b.symm j)) i hi⟩
  left_inv x := by
    apply Subtype.ext
    apply (pointsEquiv (CommRingCat.of k) c T).injective
    rw [MulEquiv.apply_symm_apply]
    apply Coordinates.ext
    · funext i
      change extendByZero (fun i => a i = 0)
        (fun j => (pointsEquiv (CommRingCat.of k) c T x.val).vec (b (b.symm j))) i =
          (pointsEquiv (CommRingCat.of k) c T x.val).vec i
      simp only [Equiv.apply_symm_apply]
      by_cases hi : a i = 0
      · simp only [extendByZero, dite_eq_left hi]
      · simp only [extendByZero, dite_eq_right hi]
        exact (diagonalKernelPoint_vec a t h T x i hi).symm
    · exact (diagonalKernelPoint_scalar a t h ht T x).symm
  right_inv y := by
    apply Multiplicative.toAdd.injective
    funext i
    change (pointsEquiv (CommRingCat.of k) c T
      ((pointsEquiv (CommRingCat.of k) c T).symm _)).vec (b i) = y.toAdd i
    rw [MulEquiv.apply_symm_apply]
    change extendByZero (fun i => a i = 0) (fun j => y.toAdd (b.symm j)) (b i) = _
    rw [extendByZero_apply, Equiv.symm_apply_apply]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    change (pointsEquiv (CommRingCat.of k) c T (x.val * y.val)).vec (b i) = _
    rw [map_mul]
    rfl

/-- Vector coordinates on the actual nonzero-scalar scheme-theoretic kernel. -/
def diagonalNonzeroKernelCoordinates (ht : t ≠ 0) {n : ℕ} (b : Fin n ≃ kernelIndices a)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) ≃*
      Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  (kernelPointsEquiv (diagonalHom (CommRingCat.of k) a t h) T).trans
    (diagonalNonzeroKernelPointEquiv a t h ht b T)

theorem diagonalNonzeroKernelCoordinates_naturality (ht : t ≠ 0) {n : ℕ}
    (b : Fin n ≃ kernelIndices a) {T T' : Over (Spec (CommRingCat.of k))}
    (f : T' ⟶ T) (x : T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) :
    (diagonalNonzeroKernelCoordinates a t h ht b T' (f ≫ x)).toAdd =
      fun i => f.left.appTop ((diagonalNonzeroKernelCoordinates a t h ht b T x).toAdd i) := by
  funext i
  change (pointsEquiv (CommRingCat.of k) c T'
    ((f ≫ x) ≫ (kernelι (diagonalHom (CommRingCat.of k) a t h)).hom.hom)).vec (b i) = _
  rw [Category.assoc, pointsEquiv_naturality]
  rfl

/-- A nonzero scalar coefficient gives an actual vector-group kernel. -/
theorem diagonalNonzeroKernel_isVectorGroup (ht : t ≠ 0) :
    RelativeRoot.IsVectorGroupOfDimension (kernel (diagonalHom (CommRingCat.of k) a t h))
      (Fintype.card (kernelIndices a)) :=
  ⟨diagonalNonzeroKernelCoordinates a t h ht (Fintype.equivFin (kernelIndices a)).symm,
    fun _ _ => diagonalNonzeroKernelCoordinates_naturality a t h ht
      (Fintype.equivFin (kernelIndices a)).symm⟩

/-- The nonzero-scalar kernel is isomorphic to the polynomial vector group. -/
def diagonalNonzeroKernelIso (ht : t ≠ 0) :
    kernel (diagonalHom (CommRingCat.of k) a t h) ≅
      VectorGroup.groupScheme (CommRingCat.of k) (Fintype.card (kernelIndices a)) :=
  RelativeRoot.vectorGroupIso
    (diagonalNonzeroKernelCoordinates a t h ht (Fintype.equivFin (kernelIndices a)).symm)
    (fun _ _ => diagonalNonzeroKernelCoordinates_naturality a t h ht
      (Fintype.equivFin (kernelIndices a)).symm)

@[simp]
theorem coordinates_diagonalNonzeroKernelIso_hom (ht : t ≠ 0)
    (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (kernel (diagonalHom (CommRingCat.of k) a t h)).X) :
    VectorGroup.coordinates (CommRingCat.of k) (Fintype.card (kernelIndices a)) T
        (x ≫ (diagonalNonzeroKernelIso a t h ht).hom.hom.hom) =
      diagonalNonzeroKernelCoordinates a t h ht (Fintype.equivFin (kernelIndices a)).symm T x :=
  RelativeRoot.coordinates_comp_vectorGroupIso_hom _ _ T x

/-- All compatible diagonal bilinear maps over a field have smooth, connected,
unipotent actual kernels, including zero-dimensional and equality cases. -/
theorem diagonal_kernel_properties :
    Smooth (kernel (diagonalHom (CommRingCat.of k) a t h)).X.hom ∧
      ConnectedSpace (kernel (diagonalHom (CommRingCat.of k) a t h)).X.left ∧
        IsUnipotent (kernel (diagonalHom (CommRingCat.of k) a t h)) := by
  by_cases ht : t = 0
  · refine smooth_connected_unipotent_of_groupIso (diagonalZeroKernelIso a t h ht)
      ⟨smooth _ _, ?_, isUnipotent k _⟩
    change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Option (kernelIndices a)) k)))
    infer_instance
  · have hv := diagonalNonzeroKernel_isVectorGroup a t h ht
    exact ⟨hv.smooth, hv.connectedSpace, hv.isUnipotent⟩

end Field

section Specialization

variable {R : CommRingCat.{u}} {k : Type u} [Field k] {I : Type u} [Fintype I]
  {c d : I → I → R}

/-- Ring-to-field specialization of a compatible diagonal map has a smooth,
connected, unipotent scheme-theoretic kernel, independently of which
coefficients vanish in the field. -/
theorem diagonal_baseChange_kernel_properties (ρ : R ⟶ CommRingCat.of k)
    (a : I → R) (t : R) (h : IsCompatible c d (diagonalMatrix a) t) :
    Smooth (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (diagonalHom R a t h))).X.hom ∧
      ConnectedSpace
        (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (diagonalHom R a t h))).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (Spec.map ρ)).map (diagonalHom R a t h))) := by
  have hh := h.map ρ.hom
  rw [map_diagonalMatrix] at hh
  have hs := linearHom_baseChange ρ (diagonalMatrix a) t h
  simp only [map_diagonalMatrix] at hs
  exact smooth_connected_unipotent_of_groupIso
    (kernelSquareIso _ _ (baseChangeIso ρ c) (baseChangeIso ρ d) hs)
    (diagonal_kernel_properties (fun i => ρ.hom (a i)) (ρ.hom t) hh)

end Specialization

end Langlands.GroupScheme.BilinearCoordinate
