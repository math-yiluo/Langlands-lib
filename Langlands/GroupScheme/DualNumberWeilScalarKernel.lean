import Langlands.GroupScheme.DualNumberWeilKernel

/-! # Scalar kernels on the actual dual-number Weil group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DualNumberWeil

variable (k : Type u) [Field k]

/-- Additive multiplication by a dual number. -/
def scalarHom {A : Type u} [CommRing A] (c : DualNumber A) :
    Multiplicative (DualNumber A) →* Multiplicative (DualNumber A) :=
  MonoidHom.mk' (fun z => Multiplicative.ofAdd (c * z.toAdd))
    (fun x y => congrArg Multiplicative.ofAdd (mul_add _ x.toAdd y.toAdd))

variable (c : DualNumber k) (S : Over (Spec (CommRingCat.of k)))

/-- The scalar over the relative global sections of a test scheme. -/
def scalarElement : DualNumber Γ(S.left, ⊤) :=
  GeneralLinear.DualNumber.coefficientMap
    (algebraMap k (((algΓ (CommRingCat.of k)).obj S).unop)) c

variable {S}

theorem scalarElement_comp {S' : Over (Spec (CommRingCat.of k))} (a : S' ⟶ S) :
    GeneralLinear.DualNumber.coefficientMap a.left.appTop.hom (scalarElement k c S) =
      scalarElement k c S' := by
  apply TrivSqZeroExt.ext
  · exact (((algΓ (CommRingCat.of k)).map a).unop.hom).commutes c.fst
  · exact (((algΓ (CommRingCat.of k)).map a).unop.hom).commutes c.snd

variable (S)

/-- Multiplication by a base dual number in the actual all-test coordinates. -/
def scalarPoints : (S ⟶ (groupScheme k).X) →* (S ⟶ (groupScheme k).X) :=
  (coordinates k S).symm.toMonoidHom.comp
    ((scalarHom (scalarElement k c S)).comp (coordinates k S).toMonoidHom)

@[simp]
theorem coordinates_scalarPoints (p : S ⟶ (groupScheme k).X) :
    coordinates k S (scalarPoints k c S p) =
      Multiplicative.ofAdd (scalarElement k c S * (coordinates k S p).toAdd) :=
  (coordinates k S).apply_symm_apply _

variable {S}

theorem scalarPoints_naturality {S' : Over (Spec (CommRingCat.of k))}
    (a : S' ⟶ S) (p : S ⟶ (groupScheme k).X) :
    scalarPoints k c S' (a ≫ p) = a ≫ scalarPoints k c S p := by
  apply (coordinates k S').injective
  rw [coordinates_scalarPoints, coordinates_comp, coordinates_comp, coordinates_scalarPoints]
  simp only [toAdd_ofAdd, map_mul, scalarElement_comp]

/-- The actual scheme map multiplying the additive dual-number coordinate by `c`. -/
def scalarMap : groupScheme k ⟶ groupScheme k :=
  homOfPoints (scalarPoints k c) (scalarPoints_naturality k c)

@[simp]
theorem coordinates_scalarMap (p : S ⟶ (groupScheme k).X) :
    coordinates k S (p ≫ (scalarMap k c).hom.hom) =
      Multiplicative.ofAdd (scalarElement k c S * (coordinates k S p).toAdd) := by
  rw [scalarMap, comp_homOfPoints]
  exact coordinates_scalarPoints k c S p

/-- The general scalar construction recovers the previously constructed epsilon map. -/
theorem scalarMap_epsilon : scalarMap k DualNumber.eps = epsilonMap k := by
  apply hom_ext_points
  intro S p
  apply (coordinates k S).injective
  rw [coordinates_scalarMap, coordinates_epsilonMap]
  simp only [scalarElement, GeneralLinear.DualNumber.coefficientMap_eps]

/-- Scalar annihilation describes the actual pointwise kernel. -/
theorem scalarMap_eq_one_iff (p : S ⟶ (groupScheme k).X) :
    p ≫ (scalarMap k c).hom.hom = 1 ↔
      scalarElement k c S * (coordinates k S p).toAdd = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun q => (coordinates k S q).toAdd) h
    simpa only [coordinates_scalarMap, map_one, toAdd_ofAdd, toAdd_one] using h'
  · intro h
    apply (coordinates k S).injective
    rw [coordinates_scalarMap, map_one]
    exact congrArg Multiplicative.ofAdd h

section CoefficientCalculation

variable {k} {A : Type u} [CommRing A] [Algebra k A]

/-- A nonzero field coefficient remains cancellable on every coefficient algebra. -/
theorem coefficient_mul_eq_zero_iff {a : k} (ha : a ≠ 0) (x : A) :
    algebraMap k A a * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun y => algebraMap k A a⁻¹ * y) h
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one,
      one_mul, mul_zero] using h'
  · intro h
    simp [h]

/-- A scalar with nonzero constant term has zero annihilator on every algebra. -/
theorem scalar_mul_eq_zero_iff_of_fst_ne_zero (hc : c.fst ≠ 0) (z : DualNumber A) :
    GeneralLinear.DualNumber.coefficientMap (algebraMap k A) c * z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hf := congrArg TrivSqZeroExt.fst h
    have hs := congrArg TrivSqZeroExt.snd h
    have hz : z.fst = 0 := (coefficient_mul_eq_zero_iff hc z.fst).mp hf
    apply TrivSqZeroExt.ext hz
    apply (coefficient_mul_eq_zero_iff hc z.snd).mp
    simpa only [DualNumber.snd_mul, GeneralLinear.DualNumber.coefficientMap_fst,
      GeneralLinear.DualNumber.coefficientMap_snd, hz, mul_zero, add_zero,
      TrivSqZeroExt.snd_zero] using hs
  · intro h
    simp [h]

/-- A nonzero pure epsilon scalar has precisely the pure epsilon annihilator. -/
theorem scalar_mul_eq_zero_iff_of_fst_eq_zero (hf : c.fst = 0) (hs : c.snd ≠ 0)
    (z : DualNumber A) :
    GeneralLinear.DualNumber.coefficientMap (algebraMap k A) c * z = 0 ↔
      z.fst = 0 := by
  constructor
  · intro h
    apply (coefficient_mul_eq_zero_iff hs z.fst).mp
    have h' := congrArg TrivSqZeroExt.snd h
    simpa only [DualNumber.snd_mul, GeneralLinear.DualNumber.coefficientMap_fst,
      GeneralLinear.DualNumber.coefficientMap_snd, hf, map_zero, zero_mul,
      zero_add, TrivSqZeroExt.snd_zero] using h'
  · intro h
    apply TrivSqZeroExt.ext
    · simp [hf]
    · simp [hf, h]

end CoefficientCalculation

/-- A scalar with nonzero constant term kills exactly the identity point. -/
theorem scalarMap_eq_one_iff_of_fst_ne_zero (hc : c.fst ≠ 0)
    (p : S ⟶ (groupScheme k).X) :
    p ≫ (scalarMap k c).hom.hom = 1 ↔ p = 1 := by
  refine (scalarMap_eq_one_iff k c p).trans ?_
  refine (scalar_mul_eq_zero_iff_of_fst_ne_zero
    (A := (((algΓ (CommRingCat.of k)).obj S).unop)) c hc _).trans ?_
  constructor
  · intro h
    apply (coordinates k S).injective
    apply Multiplicative.toAdd.injective
    simpa only [map_one, toAdd_one] using h
  · intro h
    subst p
    exact congrArg Multiplicative.toAdd ((coordinates k S).map_one)

/-- A nonzero pure epsilon scalar kills exactly points with zero constant coordinate. -/
theorem scalarMap_eq_one_iff_of_fst_eq_zero (hf : c.fst = 0) (hs : c.snd ≠ 0)
    (p : S ⟶ (groupScheme k).X) :
    p ≫ (scalarMap k c).hom.hom = 1 ↔ (coordinates k S p).toAdd.fst = 0 :=
  (scalarMap_eq_one_iff k c p).trans
    (scalar_mul_eq_zero_iff_of_fst_eq_zero
      (A := (((algΓ (CommRingCat.of k)).obj S).unop)) c hf hs _)

variable (S)

/-- The pointwise kernel of a scalar with nonzero constant term is trivial. -/
def unitScalarKernelPointEquiv (hc : c.fst ≠ 0) :
    (((yonedaGrp.map (scalarMap k c)).app (op S)).hom.ker) ≃*
      Multiplicative (Fin 0 → Γ(S.left, ⊤)) where
  toFun _ := 1
  invFun _ := ⟨1, map_one _⟩
  left_inv x := by
    apply Subtype.ext
    exact ((scalarMap_eq_one_iff_of_fst_ne_zero k c hc x.val).mp x.property).symm
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    exact Fin.elim0 i
  map_mul' _ _ := (one_mul 1).symm

/-- Natural dimension-zero coordinates on the actual kernel of a unit scalar. -/
def unitScalarKernelCoordinates (hc : c.fst ≠ 0) :
    (S ⟶ (kernel (scalarMap k c)).X) ≃*
      Multiplicative (Fin 0 → Γ(S.left, ⊤)) :=
  (kernelPointsEquiv (scalarMap k c) S).trans (unitScalarKernelPointEquiv k c S hc)

theorem unitScalarKernel_isVectorGroup (hc : c.fst ≠ 0) :
    RelativeRoot.IsVectorGroupOfDimension (kernel (scalarMap k c)) 0 := by
  refine ⟨fun S => unitScalarKernelCoordinates k c S hc, ?_⟩
  intro S S' a p
  funext i
  exact Fin.elim0 i

/-- A nonzero pure epsilon scalar leaves precisely the epsilon coefficient in its kernel. -/
def nilpotentScalarKernelPointEquiv (hf : c.fst = 0) (hs : c.snd ≠ 0) :
    (((yonedaGrp.map (scalarMap k c)).app (op S)).hom.ker) ≃*
      Multiplicative Γ(S.left, ⊤) where
  toFun x := Multiplicative.ofAdd (coordinates k S x.val).toAdd.snd
  invFun b := ⟨(coordinates k S).symm
    (Multiplicative.ofAdd (TrivSqZeroExt.inr b.toAdd)), by
      change (coordinates k S).symm _ ≫ (scalarMap k c).hom.hom = 1
      rw [scalarMap_eq_one_iff_of_fst_eq_zero k c hf hs, MulEquiv.apply_symm_apply]
      rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply (coordinates k S).injective
    rw [MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    apply TrivSqZeroExt.ext
    · exact ((scalarMap_eq_one_iff_of_fst_eq_zero k c hf hs x.val).mp x.property).symm
    · rfl
  right_inv b := by
    change Multiplicative.ofAdd
      (coordinates k S ((coordinates k S).symm _)).toAdd.snd = b
    rw [MulEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (coordinates k S (x.val * y.val)).toAdd.snd = _
    rw [map_mul]
    rfl

/-- The actual pure epsilon scalar kernel has one additive coordinate. -/
def nilpotentScalarKernelCoordinates (hf : c.fst = 0) (hs : c.snd ≠ 0) :
    (S ⟶ (kernel (scalarMap k c)).X) ≃* Multiplicative Γ(S.left, ⊤) :=
  (kernelPointsEquiv (scalarMap k c) S).trans
    (nilpotentScalarKernelPointEquiv k c S hf hs)

theorem nilpotentScalarKernelCoordinates_apply (hf : c.fst = 0) (hs : c.snd ≠ 0)
    (p : S ⟶ (kernel (scalarMap k c)).X) :
    nilpotentScalarKernelCoordinates k c S hf hs p =
      Multiplicative.ofAdd
        (coordinates k S (p ≫ (kernelι (scalarMap k c)).hom.hom)).toAdd.snd := rfl

variable {S}

theorem nilpotentScalarKernelCoordinates_comp (hf : c.fst = 0) (hs : c.snd ≠ 0)
    {S' : Over (Spec (CommRingCat.of k))} (a : S' ⟶ S)
    (p : S ⟶ (kernel (scalarMap k c)).X) :
    nilpotentScalarKernelCoordinates k c S' hf hs (a ≫ p) =
      Multiplicative.ofAdd
        (a.left.appTop (nilpotentScalarKernelCoordinates k c S hf hs p).toAdd) := by
  rw [nilpotentScalarKernelCoordinates_apply, Category.assoc, coordinates_comp,
    nilpotentScalarKernelCoordinates_apply]
  rfl

theorem nilpotentScalarKernel_isVectorGroup (hf : c.fst = 0) (hs : c.snd ≠ 0) :
    RelativeRoot.IsVectorGroupOfDimension (kernel (scalarMap k c)) 1 := by
  refine ⟨fun S => (nilpotentScalarKernelCoordinates k c S hf hs).trans
    (singletonEquiv _).symm, ?_⟩
  intro S S' a p
  funext i
  change (nilpotentScalarKernelCoordinates k c S' hf hs (a ≫ p)).toAdd =
    a.left.appTop (nilpotentScalarKernelCoordinates k c S hf hs p).toAdd
  rw [nilpotentScalarKernelCoordinates_comp]
  rfl

/-- Two additive coefficients give the standard two vector coordinates. -/
def dualVectorEquiv (A : Type u) [CommRing A] :
    Multiplicative (DualNumber A) ≃* Multiplicative (Fin 2 → A) where
  toFun z := Multiplicative.ofAdd ![z.toAdd.fst, z.toAdd.snd]
  invFun z := Multiplicative.ofAdd (z.toAdd 0, z.toAdd 1)
  left_inv _ := rfl
  right_inv z := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl

variable (S)

/-- The actual Weil restriction has the two coefficient coordinates. -/
def vectorCoordinates :
    (S ⟶ (groupScheme k).X) ≃* Multiplicative (Fin 2 → Γ(S.left, ⊤)) :=
  (coordinates k S).trans (dualVectorEquiv _)

theorem isVectorGroup : RelativeRoot.IsVectorGroupOfDimension (groupScheme k) 2 := by
  refine ⟨vectorCoordinates k, ?_⟩
  intro S S' a p
  funext i
  change (dualVectorEquiv _ (coordinates k S' (a ≫ p))).toAdd i =
    a.left.appTop ((dualVectorEquiv _ (coordinates k S p)).toAdd i)
  rw [coordinates_comp]
  fin_cases i <;> rfl

/-- The actual dual-number Weil restriction is the standard vector group of dimension two. -/
def vectorIso : groupScheme k ≅ VectorGroup.groupScheme (CommRingCat.of k) 2 :=
  (isVectorGroup k).iso

/-- The zero scalar imposes no condition on either coordinate. -/
def zeroScalarKernelPointEquiv :
    (((yonedaGrp.map (scalarMap k 0)).app (op S)).hom.ker) ≃*
      Multiplicative (DualNumber Γ(S.left, ⊤)) where
  toFun x := coordinates k S x.val
  invFun b := ⟨(coordinates k S).symm b, by
    change (coordinates k S).symm b ≫ (scalarMap k 0).hom.hom = 1
    rw [scalarMap_eq_one_iff]
    simp [scalarElement]⟩
  left_inv x := Subtype.ext ((coordinates k S).symm_apply_apply x.val)
  right_inv b := (coordinates k S).apply_symm_apply b
  map_mul' x y := (coordinates k S).map_mul x.val y.val

/-- Both coefficients are coordinates on the actual zero-scalar kernel. -/
def zeroScalarKernelCoordinates :
    (S ⟶ (kernel (scalarMap k 0)).X) ≃*
      Multiplicative (DualNumber Γ(S.left, ⊤)) :=
  (kernelPointsEquiv (scalarMap k 0) S).trans (zeroScalarKernelPointEquiv k S)

theorem zeroScalarKernelCoordinates_apply (p : S ⟶ (kernel (scalarMap k 0)).X) :
    zeroScalarKernelCoordinates k S p =
      coordinates k S (p ≫ (kernelι (scalarMap k 0)).hom.hom) := rfl

variable {S}

theorem zeroScalarKernelCoordinates_comp {S' : Over (Spec (CommRingCat.of k))}
    (a : S' ⟶ S) (p : S ⟶ (kernel (scalarMap k 0)).X) :
    zeroScalarKernelCoordinates k S' (a ≫ p) =
      Multiplicative.ofAdd (GeneralLinear.DualNumber.coefficientMap a.left.appTop.hom
        (zeroScalarKernelCoordinates k S p).toAdd) := by
  rw [zeroScalarKernelCoordinates_apply, Category.assoc, coordinates_comp,
    zeroScalarKernelCoordinates_apply]

theorem zeroScalarKernel_isVectorGroup :
    RelativeRoot.IsVectorGroupOfDimension (kernel (scalarMap k 0)) 2 := by
  refine ⟨fun S => (zeroScalarKernelCoordinates k S).trans (dualVectorEquiv _), ?_⟩
  intro S S' a p
  funext i
  change (dualVectorEquiv _ (zeroScalarKernelCoordinates k S' (a ≫ p))).toAdd i =
    a.left.appTop ((dualVectorEquiv _ (zeroScalarKernelCoordinates k S p)).toAdd i)
  rw [zeroScalarKernelCoordinates_comp]
  fin_cases i <;> rfl

/-- The dimension of the annihilator of a dual-number scalar over the base field. -/
def scalarKernelDimension : ℕ := by
  classical
  exact if c.fst = 0 then if c.snd = 0 then 2 else 1 else 0

/-- Every scalar kernel on the actual Weil group is a vector group of the expected dimension. -/
theorem scalarKernel_isVectorGroup :
    RelativeRoot.IsVectorGroupOfDimension (kernel (scalarMap k c))
      (scalarKernelDimension k c) := by
  classical
  by_cases hf : c.fst = 0
  · by_cases hs : c.snd = 0
    · have hc : c = 0 := TrivSqZeroExt.ext hf hs
      subst c
      simpa [scalarKernelDimension] using zeroScalarKernel_isVectorGroup k
    · simpa [scalarKernelDimension, hf, hs] using
        nilpotentScalarKernel_isVectorGroup k c hf hs
  · simpa [scalarKernelDimension, hf] using unitScalarKernel_isVectorGroup k c hf

/-- An actual isomorphism of every scalar kernel with a standard vector group. -/
def scalarKernelIso :
    kernel (scalarMap k c) ≅
      VectorGroup.groupScheme (CommRingCat.of k) (scalarKernelDimension k c) :=
  (scalarKernel_isVectorGroup k c).iso

theorem scalarKernel_smooth : Smooth (kernel (scalarMap k c)).X.hom :=
  (scalarKernel_isVectorGroup k c).smooth

theorem scalarKernel_connected : ConnectedSpace (kernel (scalarMap k c)).X.left :=
  (scalarKernel_isVectorGroup k c).connectedSpace

theorem scalarKernel_unipotent : IsUnipotent (kernel (scalarMap k c)) :=
  (scalarKernel_isVectorGroup k c).isUnipotent

end Langlands.GroupScheme.DualNumberWeil
