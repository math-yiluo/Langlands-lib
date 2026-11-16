import Langlands.GroupScheme.Reductive.RankOneRingRelation

/-! # The normalized Weyl product from the ring rank-one relation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RingRootCell.WeylData

variable {R : Type u} [CommRing R] (D : WeylData R)
  {Z : Over (Spec (CommRingCat.of R))}

/-- The normalized three-factor Weyl product at an arbitrary test. -/
def normalizedWeylPoint (Z : Over (Spec (CommRingCat.of R))) : Z ⟶ D.G.X :=
  D.B (-pb Z D.cβ) * (D.A 1 * D.B (-pb Z D.cβ))

/-- The normalized product is the restriction of its value over the base. -/
theorem normalizedWeylPoint_eq_constant :
    D.normalizedWeylPoint Z =
      D.G.constantPoint (D.normalizedWeylPoint (base R)) Z := by
  change _ = toBase Z ≫ D.normalizedWeylPoint (base R)
  simp only [normalizedWeylPoint, MonObj.comp_mul, CellData.comp_B,
    CellData.comp_A, map_one, map_neg, comp_pb]

/-- The rank-one relation controls rescaling of the normalized product by
every unit, including units whose difference from one is not a unit. -/
theorem normalizedWeylPoint_rescale [IsAffine D.G.X.left]
    (q : Γ(Z.left, ⊤)ˣ) :
    D.H q *
        (D.B (-pb Z D.cβ * (q : Γ(Z.left, ⊤))) *
          (D.A (↑q⁻¹ : Γ(Z.left, ⊤)) *
            D.B (-pb Z D.cβ * (q : Γ(Z.left, ⊤))))) =
      D.normalizedWeylPoint Z := by
  let β := pb Z D.cβ
  have hrel := D.relation (Z := Z) 1 ((q : Γ(Z.left, ⊤)) - 1) q (by ring)
  simp only [CellData.cellPt, mul_one] at hrel
  change D.A 1 * D.B (β * ((q : Γ(Z.left, ⊤)) - 1)) =
    D.B (β * ((↑q⁻¹ : Γ(Z.left, ⊤)) * ((q : Γ(Z.left, ⊤)) - 1))) *
      (D.H q * D.A (↑q⁻¹ : Γ(Z.left, ⊤))) at hrel
  have hshift : -β + β * ((↑q⁻¹ : Γ(Z.left, ⊤)) *
      ((q : Γ(Z.left, ⊤)) - 1)) = -β * (↑q⁻¹ : Γ(Z.left, ⊤)) := by
    have hq := Units.inv_mul q
    linear_combination β * hq
  have hweight :
      (↑(cu D.α (D.tH q))⁻¹ : Γ(Z.left, ⊤)) * (-β * (q : Γ(Z.left, ⊤))) =
        -β * (↑q⁻¹ : Γ(Z.left, ⊤)) := by
    rw [cu_tH]
    simp only [mul_inv_rev, Units.val_mul]
    calc
      _ = (-β * (↑q⁻¹ : Γ(Z.left, ⊤))) *
          ((↑q⁻¹ : Γ(Z.left, ⊤)) * (q : Γ(Z.left, ⊤))) := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]
  calc
    _ = D.B (-β * (↑q⁻¹ : Γ(Z.left, ⊤))) *
        (D.H q * (D.A (↑q⁻¹ : Γ(Z.left, ⊤)) *
          D.B (-β * (q : Γ(Z.left, ⊤))))) := by
      rw [← mul_assoc, H, CellData.I_mul_B, hweight]
      simp only [β, mul_assoc]
    _ = D.B (-β) *
        (D.B (β * ((↑q⁻¹ : Γ(Z.left, ⊤)) * ((q : Γ(Z.left, ⊤)) - 1))) *
          (D.H q * D.A (↑q⁻¹ : Γ(Z.left, ⊤)))) *
            D.B (-β * (q : Γ(Z.left, ⊤))) := by
      rw [← hshift, CellData.B_add]
      simp only [mul_assoc]
    _ = D.B (-β) * (D.A 1 * D.B (β * ((q : Γ(Z.left, ⊤)) - 1))) *
        D.B (-β * (q : Γ(Z.left, ⊤))) := by
      rw [← hrel]
    _ = D.normalizedWeylPoint Z := by
      unfold normalizedWeylPoint
      simp only [mul_assoc]
      rw [← CellData.B_add]
      congr 2
      congr 1
      ring

/-- Evaluation of the actual reflection is torus multiplication by the
inverse coroot value of the root character. -/
theorem I_reflection (t : Z ⟶ D.T.X) :
    D.I (t ≫ (CommGroupScheme.groupHom (reflectionIso D.α D.h D.hh).hom).hom.hom) =
      D.I t * (D.H (cu D.α t))⁻¹ := by
  have hneg : t ≫ (CommGroupScheme.groupHom (-(D.α ≫ D.h))).hom.hom =
      (t ≫ (CommGroupScheme.groupHom (D.α ≫ D.h)).hom.hom)⁻¹ :=
    congrArg Additive.toMul ((evalPoint t).map_neg (D.α ≫ D.h))
  have hid : t ≫ (CommGroupScheme.groupHom (𝟙 D.T)).hom.hom = t := by
    change t ≫ 𝟙 D.T.X = t
    exact Category.comp_id _
  have hc : t ≫ (CommGroupScheme.groupHom (D.α ≫ D.h)).hom.hom =
      D.tH (cu D.α t) := by
    rw [comp_groupHom_comp]
    unfold tH cu
    rw [MulEquiv.symm_apply_apply, Category.assoc]
  change D.I (t ≫ (CommGroupScheme.groupHom (𝟙 D.T - D.α ≫ D.h)).hom.hom) = _
  rw [sub_eq_add_neg, comp_groupHom_add, hneg, hid, hc,
    CellData.I_mul, CellData.I_inv]
  rfl

/-- The normalized product conjugates the torus by the actual reflection
over every test scheme, retaining nilpotent structure. -/
theorem normalizedWeylPoint_conj [IsAffine D.G.X.left] (t : Z ⟶ D.T.X) :
    D.normalizedWeylPoint Z * D.I t * (D.normalizedWeylPoint Z)⁻¹ =
      D.I (t ≫ (CommGroupScheme.groupHom (reflectionIso D.α D.h D.hh).hom).hom.hom) := by
  let q := cu D.α t
  let β := pb Z D.cβ
  have hw :
      D.normalizedWeylPoint Z * D.I t =
        D.I t *
          (D.B (-β * (q : Γ(Z.left, ⊤))) *
            (D.A (↑q⁻¹ : Γ(Z.left, ⊤)) *
              D.B (-β * (q : Γ(Z.left, ⊤))))) := by
    unfold normalizedWeylPoint
    calc
      _ = D.B (-β) * (D.A 1 * (D.B (-β) * D.I t)) := by
        simp only [β, mul_assoc]
      _ = _ := by
        rw [CellData.B_mul_I, ← mul_assoc (D.A 1), CellData.A_mul_I, mul_one]
        simp only [mul_assoc]
        rw [← mul_assoc (D.B (-β)) (D.I t), CellData.B_mul_I]
        simp only [q, mul_assoc, mul_comm (cu D.α t : Γ(Z.left, ⊤)) (-β)]
  have hres := D.normalizedWeylPoint_rescale (Z := Z) q
  have hres' :
      D.B (-β * (q : Γ(Z.left, ⊤))) *
          (D.A (↑q⁻¹ : Γ(Z.left, ⊤)) * D.B (-β * (q : Γ(Z.left, ⊤)))) =
        (D.H q)⁻¹ * D.normalizedWeylPoint Z :=
    (eq_inv_mul_iff_mul_eq).mpr hres
  rw [hw, hres', ← mul_assoc, mul_inv_cancel_right, D.I_reflection]

/-- The base normalized product is an actual normalizing point. -/
theorem normalizedWeylPoint_isNormalizing [IsAffine D.G.X.left] :
    IsNormalizingPoint D.i (D.normalizedWeylPoint (base R))
      (reflectionIso D.α D.h D.hh) := by
  apply hom_ext_points
  intro Z t
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [comp_innerIso_hom, ← D.normalizedWeylPoint_eq_constant]
  exact D.normalizedWeylPoint_conj t

end Langlands.GroupScheme.RingRootCell.WeylData
