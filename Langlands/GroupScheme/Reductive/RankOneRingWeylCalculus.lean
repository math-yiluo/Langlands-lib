import Langlands.GroupScheme.Reductive.RankOneRingNormalizedWeyl

/-! # Square and root conjugation for the normalized rank-one Weyl product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RingRootCell

namespace UnitSumExtension

variable {R : Type u} [CommRing R]

/-- In an injective extension, every element is a sum of two elements whose
complements are units. -/
theorem exists_complement_units (x : R) :
    ∃ (a b : Ring R) (q r : (Ring R)ˣ),
      inclusion x = a + b ∧
      (q : Ring R) = 1 - a ∧ (r : Ring R) = 1 - b := by
  let f := algebraMap (Polynomial R) (Ring R)
  have hq : IsUnit (f (1 - Polynomial.X)) := by
    apply IsLocalization.map_units (M := nonZeroDivisors (Polynomial R)) (Ring R) ⟨_, ?_⟩
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    simpa [Polynomial.coeff_one] using
      ((isUnit_one : IsUnit (1 : R)).neg).mem_nonZeroDivisors
  have hr : IsUnit (f (1 - Polynomial.C x + Polynomial.X)) := by
    apply IsLocalization.map_units (M := nonZeroDivisors (Polynomial R)) (Ring R) ⟨_, ?_⟩
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    simp [Polynomial.coeff_one]
  refine ⟨f Polynomial.X, f (Polynomial.C x - Polynomial.X), hq.unit, hr.unit,
    ?_, ?_, ?_⟩
  · simp only [map_sub, inclusion, RingHom.comp_apply]
    ring
  · simp only [IsUnit.unit_spec, map_sub, map_one]
  · simp only [IsUnit.unit_spec, map_add, map_sub, map_one]
    ring

end UnitSumExtension

/-- An affine test admits an injective refinement where a coordinate is a sum
of two elements with invertible complements. -/
theorem exists_complementUnit_test {S : Scheme.{u}} (Z : Over S) [IsAffine Z.left]
    (x : Γ(Z.left, ⊤)) :
    ∃ (W : Over S) (j : W ⟶ Z), Function.Injective j.left.appTop ∧
      ∃ (a b : Γ(W.left, ⊤)) (q r : Γ(W.left, ⊤)ˣ),
        j.left.appTop x = a + b ∧
        (q : Γ(W.left, ⊤)) = 1 - a ∧ (r : Γ(W.left, ⊤)) = 1 - b := by
  let B := UnitSumExtension.Ring Γ(Z.left, ⊤)
  let f : Γ(Z.left, ⊤) ⟶ CommRingCat.of B :=
    CommRingCat.ofHom UnitSumExtension.inclusion
  let j₀ : Spec (CommRingCat.of B) ⟶ Z.left := Spec.map f ≫ Z.left.isoSpec.inv
  let W : Over S := Over.mk (j₀ ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk j₀
  have hj : j.left.appTop = f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv :=
    appTop_specMap_isoSpec_inv f
  let g := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  obtain ⟨a, b, q, r, hx, hq, hr⟩ := UnitSumExtension.exists_complement_units x
  refine ⟨W, j, ?_, g a, g b, Units.map g.toMonoidHom q,
    Units.map g.toMonoidHom r, ?_, ?_, ?_⟩
  · rw [hj]
    exact ((ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1).comp
        UnitSumExtension.inclusion_injective
  · rw [hj]
    change g (UnitSumExtension.inclusion x) = _
    simpa only [map_add] using congrArg g hx
  · change g (q : B) = 1 - g a
    simpa only [map_sub, map_one] using congrArg g hq
  · change g (r : B) = 1 - g b
    simpa only [map_sub, map_one] using congrArg g hr

namespace WeylData

variable {R : Type u} [CommRing R] (D : WeylData R)
  {Z W : Over (Spec (CommRingCat.of R))}

/-- The negative-root point in the coordinate normalized by the unit beta. -/
def normalizedNegativePoint (x : Γ(Z.left, ⊤)) : Z ⟶ D.G.X :=
  D.B (pb Z D.cβ * x)

/-- Naturality of the normalized Weyl product. -/
theorem comp_normalizedWeylPoint (f : W ⟶ Z) :
    f ≫ D.normalizedWeylPoint Z = D.normalizedWeylPoint W := by
  simp only [normalizedWeylPoint, MonObj.comp_mul, CellData.comp_B,
    CellData.comp_A, map_neg, map_one, comp_pb]

/-- The square of the normalized Weyl product is the coroot value at minus one. -/
theorem normalizedWeylPoint_square [IsAffine D.G.X.left] :
    D.normalizedWeylPoint Z * D.normalizedWeylPoint Z =
      D.H (-1 : Γ(Z.left, ⊤)ˣ) := by
  have h := D.normalizedWeylPoint_rescale (Z := Z) (-1)
  simp only [Units.val_neg, Units.val_one, inv_neg, inv_one, mul_neg,
    mul_one, neg_neg] at h
  have hinv :
      D.B (pb Z D.cβ) * (D.A (-1) * D.B (pb Z D.cβ)) =
        (D.normalizedWeylPoint Z)⁻¹ := by
    simp only [normalizedWeylPoint, mul_inv_rev, ← CellData.B_neg,
      ← CellData.A_neg, neg_neg, mul_assoc]
  rw [hinv] at h
  exact (eq_mul_inv_iff_mul_eq).mp h.symm

/-- Root conjugation when the complement of the coordinate is invertible. -/
theorem normalizedWeylPoint_mul_A_of_complement_unit [IsAffine D.G.X.left]
    (x : Γ(Z.left, ⊤)) (q : Γ(Z.left, ⊤)ˣ)
    (hq : (q : Γ(Z.left, ⊤)) = 1 - x) :
    D.normalizedWeylPoint Z * D.A x =
      D.B (-pb Z D.cβ * x) * D.normalizedWeylPoint Z := by
  let β := pb Z D.cβ
  have hrel := D.relation (Z := Z) (-x) 1 q (by rw [hq]; ring)
  simp only [CellData.cellPt, mul_one] at hrel
  change D.A (-x) * D.B β =
    D.B (β * (↑q⁻¹ : Γ(Z.left, ⊤))) *
      (D.H q * D.A ((↑q⁻¹ : Γ(Z.left, ⊤)) * -x)) at hrel
  have hrev := congrArg (fun g => g⁻¹) hrel
  simp only [mul_inv_rev, ← CellData.A_neg, ← CellData.B_neg,
    ← H_inv, neg_neg, mul_assoc] at hrev
  have hsum : 1 + -((↑q⁻¹ : Γ(Z.left, ⊤)) * -x) =
      (↑q⁻¹ : Γ(Z.left, ⊤)) := by
    have hi := Units.inv_mul q
    rw [hq] at hi
    linear_combination -hi
  have hweight :
      (↑(cu D.α (D.tH q⁻¹))⁻¹ : Γ(Z.left, ⊤)) *
        (↑q⁻¹ : Γ(Z.left, ⊤)) = (q : Γ(Z.left, ⊤)) := by
    rw [cu_tH]
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have hres := D.normalizedWeylPoint_rescale (Z := Z) q⁻¹
  have hleft :
      D.H q⁻¹ * D.B (-β * (↑q⁻¹ : Γ(Z.left, ⊤))) =
        D.B (-β * (q : Γ(Z.left, ⊤))) * D.H q⁻¹ := by
    rw [H, CellData.I_mul_B, cu_tH]
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    congr 2
    have hi := Units.mul_inv q
    linear_combination -β * (q : Γ(Z.left, ⊤)) * hi
  have hβ : -β * x + -β * (q : Γ(Z.left, ⊤)) = -β := by rw [hq]; ring
  calc
    _ = D.B (-β) *
        (D.A 1 * (D.B (-β) * D.A x)) := by
      simp only [normalizedWeylPoint, β, mul_assoc]
    _ = D.B (-β) *
        (D.A (↑q⁻¹ : Γ(Z.left, ⊤)) *
          (D.H q⁻¹ * D.B (-(β * (↑q⁻¹ : Γ(Z.left, ⊤)))))) := by
      rw [hrev, ← mul_assoc (D.A 1), ← CellData.A_add, hsum]
    _ = D.B (-β) *
        (D.H q⁻¹ *
          (D.A (q : Γ(Z.left, ⊤)) *
            D.B (-β * (↑q⁻¹ : Γ(Z.left, ⊤))))) := by
      rw [← mul_assoc (D.A _), H, CellData.A_mul_I, hweight]
      simp only [neg_mul, mul_assoc]
    _ = D.B (-β * x) *
        (D.H q⁻¹ *
          (D.B (-β * (↑q⁻¹ : Γ(Z.left, ⊤))) *
            (D.A (q : Γ(Z.left, ⊤)) *
              D.B (-β * (↑q⁻¹ : Γ(Z.left, ⊤)))))) := by
      rw [← mul_assoc (D.H q⁻¹) (D.B (-β * (↑q⁻¹ : Γ(Z.left, ⊤)))), hleft]
      simp only [mul_assoc]
      rw [← mul_assoc (D.B (-β * x)) (D.B (-β * (q : Γ(Z.left, ⊤)))),
        ← CellData.B_add, hβ]
    _ = _ := by
      simpa only [inv_inv] using congrArg (D.B (-β * x) * ·) hres

/-- Root conjugation on an affine test, with no restriction on the coordinate. -/
theorem normalizedWeylPoint_mul_A_affine [IsAffine D.G.X.left] [IsAffine Z.left]
    (x : Γ(Z.left, ⊤)) :
    D.normalizedWeylPoint Z * D.A x =
      D.B (-pb Z D.cβ * x) * D.normalizedWeylPoint Z := by
  obtain ⟨W, j, hj, a, b, q, r, hx, hq, hr⟩ := exists_complementUnit_test Z x
  have ha := D.normalizedWeylPoint_mul_A_of_complement_unit a q hq
  have hb := D.normalizedWeylPoint_mul_A_of_complement_unit b r hr
  apply points_ext_of_injective_appTop j hj
  simp only [MonObj.comp_mul, comp_normalizedWeylPoint, CellData.comp_A,
    CellData.comp_B, map_mul, map_neg, comp_pb]
  rw [hx, CellData.A_add, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc,
    ← CellData.B_add]
  congr 2
  ring

/-- The normalized Weyl product carries the positive root to the negative root
with coefficient minus beta, on every scheme test. -/
theorem normalizedWeylPoint_mul_A [IsAffine D.G.X.left] (x : Γ(Z.left, ⊤)) :
    D.normalizedWeylPoint Z * D.A x =
      D.B (-pb Z D.cβ * x) * D.normalizedWeylPoint Z := by
  apply Over.OverMorphism.ext
  apply Z.left.affineCover.hom_ext
  intro i
  let V := SubgroupFunctor.coverObj Z.left.affineCover i
  let : IsAffine V.left := inferInstanceAs (IsAffine (Z.left.affineCover.X i))
  let j : V ⟶ Z := SubgroupFunctor.coverMap Z.left.affineCover i
  have h : j ≫ (D.normalizedWeylPoint Z * D.A x) =
      j ≫ (D.B (-pb Z D.cβ * x) * D.normalizedWeylPoint Z) := by
    simp only [MonObj.comp_mul, comp_normalizedWeylPoint, CellData.comp_A,
      CellData.comp_B, map_mul, map_neg, comp_pb]
    exact D.normalizedWeylPoint_mul_A_affine (j.left.appTop x)
  exact congrArg (fun f => f.left) h

/-- Positive-root conjugation by the normalized Weyl product. -/
theorem normalizedWeylPoint_conj_A [IsAffine D.G.X.left] (x : Γ(Z.left, ⊤)) :
    D.normalizedWeylPoint Z * D.A x * (D.normalizedWeylPoint Z)⁻¹ =
      D.B (-pb Z D.cβ * x) := by
  rw [normalizedWeylPoint_mul_A, mul_inv_cancel_right]

/-- Negative-root conjugation in beta-scaled coordinates. -/
theorem normalizedWeylPoint_conj_B_beta [IsAffine D.G.X.left] (x : Γ(Z.left, ⊤)) :
    D.normalizedWeylPoint Z * D.B (pb Z D.cβ * x) *
        (D.normalizedWeylPoint Z)⁻¹ = D.A (-x) := by
  have ha := D.normalizedWeylPoint_conj_A (Z := Z) (-x)
  simp only [mul_neg, neg_mul, neg_neg] at ha
  have hH : D.H (-1 : Γ(Z.left, ⊤)ˣ) * D.A (-x) *
      (D.H (-1 : Γ(Z.left, ⊤)ˣ))⁻¹ = D.A (-x) := by
    rw [H, CellData.I_mul_A, cu_tH, mul_inv_cancel_right]
    simp
  calc
    _ = (D.normalizedWeylPoint Z * D.normalizedWeylPoint Z) * D.A (-x) *
        (D.normalizedWeylPoint Z * D.normalizedWeylPoint Z)⁻¹ := by
      rw [← ha, mul_inv_rev]
      simp only [mul_assoc]
    _ = _ := by rw [normalizedWeylPoint_square]; exact hH

/-- The normalized root coordinates have the usual positive-root Weyl law. -/
theorem normalizedWeylPoint_conj_A_normalized [IsAffine D.G.X.left]
    (x : Γ(Z.left, ⊤)) :
    D.normalizedWeylPoint Z * D.A x * (D.normalizedWeylPoint Z)⁻¹ =
      D.normalizedNegativePoint (-x) := by
  simpa only [normalizedNegativePoint, mul_neg, neg_mul] using
    D.normalizedWeylPoint_conj_A x

/-- The normalized root coordinates have the usual negative-root Weyl law. -/
theorem normalizedWeylPoint_conj_normalizedNegativePoint [IsAffine D.G.X.left]
    (x : Γ(Z.left, ⊤)) :
    D.normalizedWeylPoint Z * D.normalizedNegativePoint x *
        (D.normalizedWeylPoint Z)⁻¹ = D.A (-x) :=
  D.normalizedWeylPoint_conj_B_beta x

/-- The positive-negative-positive and negative-positive-negative Weyl
products agree in normalized coordinates. -/
theorem normalizedWeylPoint_braid [IsAffine D.G.X.left] :
    D.normalizedWeylPoint Z =
      D.A 1 * (D.B (-pb Z D.cβ) * D.A 1) := by
  have h := D.normalizedWeylPoint_mul_A (Z := Z) (-1)
  simp only [mul_neg, mul_one, neg_neg] at h
  have h' : D.normalizedWeylPoint Z * D.A (-1) =
      D.A 1 * D.B (-pb Z D.cβ) := by
    rw [h, normalizedWeylPoint, ← mul_assoc, ← CellData.B_add,
      add_neg_cancel, CellData.B_zero, one_mul]
  calc
    _ = (D.normalizedWeylPoint Z * D.A (-1)) * D.A 1 := by
      rw [CellData.A_neg, mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by rw [h', mul_assoc]

end WeylData

end Langlands.GroupScheme.RingRootCell
