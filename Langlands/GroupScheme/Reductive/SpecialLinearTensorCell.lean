import Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction
import Langlands.GroupScheme.SpecialLinearBinaryRootGroups
import Langlands.GroupScheme.Reductive.SpecialLinearTorus
import Langlands.GroupScheme.Torus.InducedProducts
import Langlands.GroupScheme.UnitLocusOpenImmersion

/-! # The root cell of `SL₂ × C` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTensorCell

open RootCell (Ga crd pt)

/-! ### Matrix identities in `SL₂` -/

section Matrices

variable {A : Type*} [CommRing A]

/-- The upper unipotent matrix `[[1, a], [0, 1]]`. -/
abbrev up (a : A) : Matrix.SpecialLinearGroup (Fin 2) A :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a

/-- The lower unipotent matrix `[[1, 0], [b, 1]]`. -/
abbrev lo (b : A) : Matrix.SpecialLinearGroup (Fin 2) A :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) b

theorem coe_up (a : A) : (up a : Matrix (Fin 2) (Fin 2) A) = !![1, a; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection]

theorem coe_lo (b : A) : (lo b : Matrix (Fin 2) (Fin 2) A) = !![1, 0; b, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection]

theorem coe_torusMatrix_one (τ : ULift.{u} (Fin 1) → Aˣ) :
    (SpecialLinear.FinSucc.torusMatrix τ : Matrix (Fin 2) (Fin 2) A) =
      !![(τ ⟨0⟩ : A), 0; 0, ((τ ⟨0⟩)⁻¹ : Aˣ)] := by
  rw [SpecialLinear.FinSucc.coe_torusMatrix]
  have h0 : SpecialLinear.FinSucc.torusEntry τ 0 = τ ⟨0⟩ :=
    SpecialLinear.FinSucc.torusEntry_castSucc τ 0
  have h1 : SpecialLinear.FinSucc.torusEntry τ 1 = (τ ⟨0⟩)⁻¹ := by
    rw [SpecialLinear.FinSucc.torusEntry, Fintype.prod_unique]
    change τ default ^ SpecialLinear.FinSucc.weightCoord 1 (Fin.last 1) _ = _
    rw [SpecialLinear.FinSucc.weightCoord_last, zpow_neg_one]
    rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1]

/-- The diagonal matrix `diag(s, s⁻¹)`. -/
def dg (s : Aˣ) : Matrix.SpecialLinearGroup (Fin 2) A :=
  ⟨!![(s : A), 0; 0, ((s⁻¹ : Aˣ) : A)], by simp [Matrix.det_fin_two]⟩

theorem coe_dg (s : Aˣ) :
    (dg s : Matrix (Fin 2) (Fin 2) A) = !![(s : A), 0; 0, ((s⁻¹ : Aˣ) : A)] := rfl

theorem torusMatrix_eq_dg (τ : ULift.{u} (Fin 1) → Aˣ) :
    SpecialLinear.FinSucc.torusMatrix τ = dg (τ ⟨0⟩) :=
  Subtype.ext (coe_torusMatrix_one τ)

theorem coe_inv_two (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem dg_up_dg_inv (s : Aˣ) (a : A) :
    dg s * up a * (dg s)⁻¹ = up (((s ^ 2 : Aˣ) : A) * a) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_inv_two, coe_dg, coe_up]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

theorem dg_lo_dg_inv (s : Aˣ) (b : A) :
    dg s * lo b * (dg s)⁻¹ = lo ((((s ^ 2)⁻¹ : Aˣ) : A) * b) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_inv_two, coe_dg, coe_lo]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

theorem up_mul_lo (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    up a * lo b = lo (((u⁻¹ : Aˣ) : A) * b) * dg u * up (((u⁻¹ : Aˣ) : A) * a) := by
  have h1 : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := u.inv_mul
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dg, coe_up, coe_lo]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-1 : A) * hu
  · linear_combination (-b) * h1
  · linear_combination (-1 - ((u⁻¹ : Aˣ) : A) * a * b) * h1 + ((u⁻¹ : Aˣ) : A) * hu

/-- The cell `lo m * dg s * up p` as a matrix. -/
theorem coe_cell (m p : A) (s : Aˣ) :
    ((lo m * (dg s * up p) : Matrix.SpecialLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![(s : A), s * p; m * s, m * s * p + ((s⁻¹ : Aˣ) : A)] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dg, coe_up, coe_lo]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- A matrix whose upper left entry is a unit lies in the cell. -/
theorem eq_cell (g : Matrix.SpecialLinearGroup (Fin 2) A) (s : Aˣ) (hs : (s : A) = g 0 0) :
    g = lo (g 1 0 * ((s⁻¹ : Aˣ) : A)) * (dg s * up (((s⁻¹ : Aˣ) : A) * g 0 1)) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact g.2
  have h1 : ((s⁻¹ : Aˣ) : A) * (s : A) = 1 := s.inv_mul
  ext i j
  rw [coe_cell]
  fin_cases i <;> fin_cases j <;> simp
  · exact hs.symm
  · linear_combination ((s⁻¹ : Aˣ) : A) * hdet - g 1 1 * h1 + g 1 1 * ((s⁻¹ : Aˣ) : A) * hs

theorem up_mul_lo_apply_zero_zero (a b : A) :
    ((up a * lo b : Matrix.SpecialLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 =
      1 + a * b := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_up, coe_lo]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The cell coordinates of a matrix are unique. -/
theorem cell_injective {m p m' p' : A} {s s' : Aˣ}
    (h : lo m * (dg s * up p) = lo m' * (dg s' * up p')) : m = m' ∧ s = s' ∧ p = p' := by
  have h' := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A)) h
  simp only [coe_cell] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  simp at h00 h01 h10
  have hs : s = s' := Units.ext h00
  subst hs
  refine ⟨?_, rfl, ?_⟩
  · have := congrArg (· * ((s⁻¹ : Aˣ) : A)) h10
    simpa [mul_assoc] using this
  · have := congrArg (((s⁻¹ : Aˣ) : A) * ·) h01
    simpa [← mul_assoc] using this

/-- The Weyl matrix `[[0, 1], [-1, 0]]`. -/
def wy : Matrix.SpecialLinearGroup (Fin 2) A :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem wy_up_wy_inv (a : A) : wy * up a * wy⁻¹ = lo (-a) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_inv_two, coe_up, coe_lo]
  change (!![0, 1; -1, 0] * !![1, a; 0, 1] * !![_, _; _, _] : Matrix (Fin 2) (Fin 2) A) i j = _
  fin_cases i <;> fin_cases j <;> simp [wy, Matrix.mul_apply, Fin.sum_univ_two]

theorem wy_mul_apply_zero_zero (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ((wy : Matrix.SpecialLinearGroup (Fin 2) A) * g) 0 0 = g 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) A) * (g : Matrix (Fin 2) (Fin 2) A)) 0 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end Matrices

/-! ### The group scheme `SL₂ × C` -/

section GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] (C : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The binary special linear group scheme. -/
abbrev SL2 (k : Type u) [Field k] : GroupScheme (Spec (CommRingCat.of k)) :=
  SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)

/-- The one-dimensional split torus `𝔾ₘ`, the diagonal torus of `SL₂`. -/
abbrev Dt (k : Type u) [Field k] : CommGroupScheme (Spec (CommRingCat.of k)) :=
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} (Fin 1))

/-- The group `SL₂ × C`. It is a `def` so that instance search sees its group law
directly, rather than through the monoidal product of group objects. -/
def G₀ : GroupScheme (Spec (CommRingCat.of k)) := SL2 k ⊗ C.toGrp

/-- The commutative group scheme `𝔾ₘ × C`, the middle factor of the cell of `SL₂ × C`.
It is a split torus when `C` is one, which is the case used for the rank-one central cover.
For a general commutative `C` it need not be a torus. -/
abbrev T₀ : CommGroupScheme (Spec (CommRingCat.of k)) := CommGroupScheme.prod (Dt k) C

/-- The homomorphism `𝔾ₘ × C ⟶ SL₂ × C`: the diagonal torus of `SL₂` times the identity
of `C`. -/
abbrev i₀ : (T₀ C).toGrp ⟶ G₀ C :=
  SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k) ⊗ₘ 𝟙 C.toGrp

/-- The map `a ↦ (up a, 1)` from `𝔾ₐ` to `SL₂ × C`, built from the upper root group of
`SL₂`. -/
abbrev xp₀ : Ga k ⟶ G₀ C := lift (SpecialLinear.BinaryRoot.upperMap (CommRingCat.of k)) 1

/-- The map `b ↦ (lo b, 1)` from `𝔾ₐ` to `SL₂ × C`, built from the lower root group of
`SL₂`. -/
abbrev xm₀ : Ga k ⟶ G₀ C := lift (SpecialLinear.BinaryRoot.lowerMap (CommRingCat.of k)) 1

/-- The cell character `(τ, c) ↦ τ²` of `𝔾ₘ × C`: the root of the diagonal torus of `SL₂`,
composed with the first projection. -/
abbrev χ₀ : characterLattice (T₀ C) :=
  CommGroupScheme.prodFst (Dt k) C ≫
    ((2 : ℤ) • splitTorus.proj (Spec (CommRingCat.of k)) (ULift.{u} (Fin 1)) ⟨0⟩)

/-- The cell cocharacter `s ↦ (s, 1)` of `𝔾ₘ × C`: the coroot of the diagonal torus of `SL₂`,
followed by the first inclusion. -/
abbrev χv₀ : cocharacterLattice (T₀ C) :=
  splitTorus.single (Spec (CommRingCat.of k)) (ULift.{u} (Fin 1)) ⟨0⟩ ≫
    CommGroupScheme.prodInl (Dt k) C

/-- Points of `SL₂ × C` are pairs of a matrix and a point of `C`. -/
def ptEquiv (Z : Over (Spec (CommRingCat.of k))) :
    (Z ⟶ (G₀ C).X) ≃* Matrix.SpecialLinearGroup (Fin 2) Γ(Z.left, ⊤) × (Z ⟶ C.X) :=
  (GroupScheme.productPointsEquiv (SL2 k) C.toGrp Z).trans
    (MulEquiv.prodCongr (SpecialLinear.pointsEquiv (Fin 2) _ Z) (MulEquiv.refl _))

variable {C}

theorem ptEquiv_apply {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ (G₀ C).X) :
    ptEquiv C Z x = (SpecialLinear.pointsEquiv (Fin 2) _ Z (x ≫ fst _ _), x ≫ snd _ _) := rfl

/-- The unit coordinate of a point of `𝔾ₘ × C`. -/
def tc {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (T₀ C).X) : Γ(Z.left, ⊤)ˣ :=
  splitTorus.pointsEquiv (ULift.{u} (Fin 1)) Z (t ≫ fst _ _) ⟨0⟩

theorem i₀_hom : (i₀ C).hom.hom =
    (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k)).hom.hom ⊗ₘ 𝟙 C.X := rfl

theorem xp₀_hom : (xp₀ C).hom.hom =
    lift (SpecialLinear.BinaryRoot.upperMap (CommRingCat.of k)).hom.hom
      (1 : Ga k ⟶ C.toGrp).hom.hom := rfl

theorem xm₀_hom : (xm₀ C).hom.hom =
    lift (SpecialLinear.BinaryRoot.lowerMap (CommRingCat.of k)).hom.hom
      (1 : Ga k ⟶ C.toGrp).hom.hom := rfl

theorem i₀_fst : (i₀ C).hom.hom ≫ fst (SL2 k).X C.X =
    fst _ _ ≫ (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k)).hom.hom :=
  tensorHom_fst _ _

theorem i₀_snd : (i₀ C).hom.hom ≫ snd (SL2 k).X C.X = snd _ _ :=
  (tensorHom_snd _ _).trans (Category.comp_id _)

theorem ptEquiv_i₀ {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (T₀ C).X) :
    ptEquiv C Z (t ≫ (i₀ C).hom.hom) = (dg (tc t), t ≫ snd _ _) := by
  have h1 : (t ≫ (i₀ C).hom.hom) ≫ fst (SL2 k).X C.X =
      (t ≫ fst (Dt k).X C.X) ≫
        (SpecialLinear.FinSucc.diagonalTorus 1 (CommRingCat.of k)).hom.hom := by
    rw [Category.assoc, Category.assoc, i₀_fst]
  have h2 : (t ≫ (i₀ C).hom.hom) ≫ snd (SL2 k).X C.X = t ≫ snd (Dt k).X C.X := by
    rw [Category.assoc, i₀_snd]
  rw [ptEquiv_apply, h1, h2, SpecialLinear.FinSucc.pointsEquiv_diagonalTorus, torusMatrix_eq_dg]
  rfl

theorem one_hom_comp {Z : Over (Spec (CommRingCat.of k))} (a : Z ⟶ (Ga k).X) :
    a ≫ (1 : Ga k ⟶ C.toGrp).hom.hom = 1 := by
  rw [Grp.Hom.hom_one, Mon.Hom.hom_one]
  exact MonObj.comp_one a

theorem ptEquiv_xp₀ {Z : Over (Spec (CommRingCat.of k))} (a : Z ⟶ (Ga k).X) :
    ptEquiv C Z (a ≫ (xp₀ C).hom.hom) = (up (crd a), 1) := by
  rw [ptEquiv_apply, xp₀_hom, Category.assoc, Category.assoc, lift_fst, lift_snd,
    SpecialLinear.BinaryRoot.pointsEquiv_rootMap, one_hom_comp]

theorem ptEquiv_xm₀ {Z : Over (Spec (CommRingCat.of k))} (b : Z ⟶ (Ga k).X) :
    ptEquiv C Z (b ≫ (xm₀ C).hom.hom) = (lo (crd b), 1) := by
  rw [ptEquiv_apply, xm₀_hom, Category.assoc, Category.assoc, lift_fst, lift_snd,
    SpecialLinear.BinaryRoot.pointsEquiv_rootMap, one_hom_comp]

theorem comp_prodFst {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (T₀ C).X) :
    t ≫ (CommGroupScheme.groupHom (CommGroupScheme.prodFst (Dt k) C)).hom.hom =
      t ≫ fst (Dt k).X C.X := rfl

theorem gm_χ₀ {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (T₀ C).X) :
    Gm.pointsEquiv _ Z (t ≫ (CommGroupScheme.groupHom (χ₀ C)).hom.hom) = tc t ^ 2 := by
  rw [comp_groupHom_comp, comp_groupHom_zsmul, map_zpow, splitTorus.comp_proj, comp_prodFst]
  rfl

theorem charValue_χ₀ {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (T₀ C).X) :
    VectorGroup.charValue (χ₀ C) Z t = ((tc t ^ 2 : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  rw [VectorGroup.charValue, gm_χ₀]

theorem charValue_neg_χ₀ {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (T₀ C).X) :
    VectorGroup.charValue (-χ₀ C) Z t =
      (((tc t ^ 2)⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
  rw [VectorGroup.charValue, ← neg_one_zsmul, comp_groupHom_zsmul, map_zpow, gm_χ₀, zpow_neg,
    zpow_one]

theorem prodInl_hom_fst :
    (CommGroupScheme.groupHom (CommGroupScheme.prodInl (Dt k) C)).hom.hom ≫ fst (Dt k).X C.X =
      𝟙 _ :=
  lift_fst _ _

theorem prodInl_hom_snd :
    (CommGroupScheme.groupHom (CommGroupScheme.prodInl (Dt k) C)).hom.hom ≫ snd (Dt k).X C.X =
      (1 : (Dt k).X ⟶ C.X) :=
  lift_snd _ _

theorem ptEquiv_coroot {Z : Over (Spec (CommRingCat.of k))} (u : Γ(Z.left, ⊤)ˣ) :
    ptEquiv C Z ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom (χv₀ C)).hom.hom ≫
      (i₀ C).hom.hom) = (dg u, 1) := by
  rw [← Category.assoc, ptEquiv_i₀, comp_groupHom_comp]
  congr 1
  · congr 1
    rw [tc, Category.assoc, prodInl_hom_fst, Category.comp_id,
      splitTorus.pointsEquiv_comp_single]
    simp
  · rw [Category.assoc, prodInl_hom_snd, MonObj.comp_one]

theorem crd_weightPointAction (χ : characterLattice (T₀ C)) {Z : Over (Spec (CommRingCat.of k))}
    (t : Z ⟶ (T₀ C).X) (a : Z ⟶ (Ga k).X) :
    crd (VectorGroup.weightPointAction χ Z t a) = VectorGroup.charValue χ Z t * crd a := by
  rw [crd, VectorGroup.coordinates_weightPointAction]
  rfl

/-! ### The root cell of `SL₂ × C` -/

/-- The open-cell multiplication `(m, t, p) ↦ x₋(m) t x₊(p)` of `SL₂ × C`. -/
abbrev cell₀ (C : CommGroupScheme (Spec (CommRingCat.of k))) : RootCell.Cell (T₀ C) ⟶ (G₀ C).X :=
  Dynamic.tripleCellMultiplication (xm₀ C) (i₀ C) (xp₀ C)

theorem ptEquiv_lift_cell₀ {Z : Over (Spec (CommRingCat.of k))} (m p : Z ⟶ (Ga k).X)
    (t : Z ⟶ (T₀ C).X) :
    ptEquiv C Z (lift m (lift t p) ≫ cell₀ C) =
      (lo (crd m) * (dg (tc t) * up (crd p)), t ≫ snd _ _) := by
  rw [Dynamic.lift_tripleCellMultiplication, map_mul, map_mul, ptEquiv_xm₀, ptEquiv_i₀,
    ptEquiv_xp₀]
  ext1
  · rfl
  · change 1 * ((t ≫ snd _ _) * 1) = _
    rw [one_mul, mul_one]

theorem ptEquiv_cell₀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ RootCell.Cell (T₀ C)) :
    ptEquiv C Z (c ≫ cell₀ C) =
      (lo (crd (c ≫ fst _ _)) * (dg (tc (c ≫ snd _ _ ≫ fst _ _)) * up (crd (c ≫ snd _ _ ≫ snd _ _))),
        (c ≫ snd _ _ ≫ fst _ _) ≫ snd _ _) := by
  conv_lhs => rw [RootCell.eq_lift c]
  rw [ptEquiv_lift_cell₀]

theorem conj_xp₀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ (T₀ C).X) (a : Z ⟶ (Ga k).X) :
    (t ≫ (i₀ C).hom.hom) * (a ≫ (xp₀ C).hom.hom) * (t ≫ (i₀ C).hom.hom)⁻¹ =
      VectorGroup.weightPointAction (χ₀ C) Z t a ≫ (xp₀ C).hom.hom := by
  apply (ptEquiv C Z).injective
  rw [map_mul, map_mul, map_inv, ptEquiv_i₀, ptEquiv_xp₀, ptEquiv_xp₀, crd_weightPointAction,
    charValue_χ₀]
  ext1
  · exact dg_up_dg_inv _ _
  · change (t ≫ snd _ _) * 1 * (t ≫ snd _ _)⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

theorem conj_xm₀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ (T₀ C).X) (b : Z ⟶ (Ga k).X) :
    (t ≫ (i₀ C).hom.hom) * (b ≫ (xm₀ C).hom.hom) * (t ≫ (i₀ C).hom.hom)⁻¹ =
      VectorGroup.weightPointAction (-χ₀ C) Z t b ≫ (xm₀ C).hom.hom := by
  apply (ptEquiv C Z).injective
  rw [map_mul, map_mul, map_inv, ptEquiv_i₀, ptEquiv_xm₀, ptEquiv_xm₀, crd_weightPointAction,
    charValue_neg_χ₀]
  ext1
  · exact dg_lo_dg_inv _ _
  · change (t ≫ snd _ _) * 1 * (t ≫ snd _ _)⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

theorem mul_eq₀ (Z : Over (Spec (CommRingCat.of k))) (a b a' b' : Z ⟶ (Ga k).X)
    (u : (Γ(Z.left, ⊤))ˣ) (hu : (u : Γ(Z.left, ⊤)) = 1 + crd a * crd b)
    (ha : crd a' = ↑u⁻¹ * crd a) (hb : crd b' = ↑u⁻¹ * crd b) :
    (a ≫ (xp₀ C).hom.hom) * (b ≫ (xm₀ C).hom.hom) =
      (b' ≫ (xm₀ C).hom.hom) *
        ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom (χv₀ C)).hom.hom ≫
          (i₀ C).hom.hom) * (a' ≫ (xp₀ C).hom.hom) := by
  apply (ptEquiv C Z).injective
  rw [map_mul, map_mul, map_mul, ptEquiv_xp₀, ptEquiv_xm₀, ptEquiv_xm₀, ptEquiv_xp₀,
    ptEquiv_coroot, ha, hb]
  ext1
  · exact up_mul_lo _ _ u hu
  · change (1 : Z ⟶ C.X) * 1 = 1 * 1 * 1
    rw [one_mul, one_mul]

theorem exists_iff₀ (Z : Over (Spec (CommRingCat.of k))) (a b : Z ⟶ (Ga k).X) :
    (∃ c, c ≫ cell₀ C = (a ≫ (xp₀ C).hom.hom) * (b ≫ (xm₀ C).hom.hom)) ↔
      IsUnit (1 + crd a * crd b) := by
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg
      (fun x => ((ptEquiv C Z x).1 : Matrix (Fin 2) (Fin 2) Γ(Z.left, ⊤)) 0 0) hc
    simp only [ptEquiv_cell₀, map_mul, Prod.fst_mul, ptEquiv_xp₀, ptEquiv_xm₀, coe_cell,
      up_mul_lo_apply_zero_zero] at h
    rw [← h]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨lift (pt (↑u⁻¹ * crd b)) (lift (RootCell.coU (χv₀ C) u) (pt (↑u⁻¹ * crd a))), ?_⟩
    rw [Dynamic.lift_tripleCellMultiplication, mul_eq₀ Z a b (pt (↑u⁻¹ * crd a))
      (pt (↑u⁻¹ * crd b)) u hu (RootCell.crd_pt _) (RootCell.crd_pt _), mul_assoc,
      RootCell.coU, Category.assoc]

variable (C) in
/-- The upper left matrix entry, as a global function on `SL₂ × C`. -/
def g₀ : Γ((G₀ C).X.left, ⊤) :=
  (fst (SL2 k).X C.X).left.appTop (SpecialLinear.entrySection (Fin 2) (CommRingCat.of k) 0 0)

theorem appTop_g₀ {Z : Over (Spec (CommRingCat.of k))} (y : Z ⟶ (G₀ C).X) :
    y.left.appTop (g₀ C) = (ptEquiv C Z y).1 0 0 := by
  rw [ptEquiv_apply, SpecialLinear.pointsEquiv_apply_apply]
  rfl

instance mono_cell₀ : Mono (cell₀ C) := by
  constructor
  intro Z c c' h
  have h' := congrArg (ptEquiv C Z) h
  rw [ptEquiv_cell₀, ptEquiv_cell₀] at h'
  obtain ⟨hM, hC⟩ := Prod.mk.inj h'
  obtain ⟨hm, hs, hp⟩ := cell_injective hM
  have ht : c ≫ snd _ _ ≫ fst _ _ = c' ≫ snd _ _ ≫ fst _ _ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply (splitTorus.pointsEquiv (ULift.{u} (Fin 1)) Z).injective
      funext j
      obtain ⟨j⟩ := j
      obtain rfl := Fin.fin_one_eq_zero j
      exact hs
    · exact hC
  rw [RootCell.eq_lift c, RootCell.eq_lift c', RootCell.crd_injective hm,
    RootCell.crd_injective hp, ht]

theorem isOpenImmersion_cell₀ : IsOpenImmersion (cell₀ C).left := by
  refine UnitLocus.isOpenImmersion_of_unitLocus (cell₀ C) (g₀ C) ?_ ?_
  · have h := appTop_g₀ (C := C) (𝟙 (RootCell.Cell (T₀ C)) ≫ cell₀ C)
    rw [ptEquiv_cell₀, coe_cell] at h
    simp only [Category.id_comp] at h
    rw [h]
    simp
  · intro Z y hy
    rw [appTop_g₀] at hy
    obtain ⟨s, hs⟩ := hy
    obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : Z ⟶ (T₀ C).X, tc τ = s ∧ τ ≫ snd _ _ = y ≫ snd _ _ :=
      ⟨lift ((splitTorus.pointsEquiv (ULift.{u} (Fin 1)) Z).symm fun _ => s) (y ≫ snd _ _),
        by rw [tc, lift_fst, MulEquiv.apply_symm_apply], lift_snd _ _⟩
    refine ⟨lift (pt ((ptEquiv C Z y).1 1 0 * ↑s⁻¹))
      (lift τ (pt (↑s⁻¹ * (ptEquiv C Z y).1 0 1))), ?_⟩
    apply (ptEquiv C Z).injective
    rw [ptEquiv_lift_cell₀, RootCell.crd_pt, RootCell.crd_pt, hτ1, hτ2, ← eq_cell _ s hs]
    rfl

/-- **The root cell of `SL₂ × C`**, in the sense of `RootCell.IsRootCell`, for every
commutative group scheme `C` over `k`. -/
theorem isRootCell₀ : RootCell.IsRootCell (i₀ C) (χ₀ C) (χv₀ C) (xp₀ C) (xm₀ C) where
  conj_xp := conj_xp₀
  conj_xm := conj_xm₀
  isOpenImmersion := isOpenImmersion_cell₀
  exists_iff := exists_iff₀
  mul_eq := mul_eq₀

end GroupScheme

end Langlands.GroupScheme.SpecialLinearTensorCell
