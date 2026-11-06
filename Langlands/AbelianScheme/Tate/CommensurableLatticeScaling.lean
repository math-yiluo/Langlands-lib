import Langlands.AbelianScheme.Tate.CommensurableLatticeTorsion

/-! # Rational scaling of the normalized full Tate image -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Langlands.AbelianScheme.Tate

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Scaling both reverse maps by `1/n` gives an actual rational isomorphism. -/
def squareReverseIso (n : ℕ) (hn : 0 < n) (q : A ⟶ B) (r : B ⟶ A)
    (hqr : q ≫ r = (n * n) • 𝟙 A) (hrq : r ≫ q = (n * n) • 𝟙 B) :
    Rationalization.of B ≅ Rationalization.of A where
  hom := (n : ℚ)⁻¹ ⊗ₜ[ℤ] r
  inv := (n : ℚ)⁻¹ ⊗ₜ[ℤ] q
  hom_inv_id := by
    change Rationalization.comp _ _ _
      ((n : ℚ)⁻¹ ⊗ₜ[ℤ] r) ((n : ℚ)⁻¹ ⊗ₜ[ℤ] q) = _
    rw [Rationalization.comp_tmul, hrq, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    have hnn : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hc : (n * n : ℕ) • ((n : ℚ)⁻¹ * (n : ℚ)⁻¹) = 1 := by
      rw [nsmul_eq_mul]
      push_cast
      field_simp
    rw [hc]
    rfl
  inv_hom_id := by
    change Rationalization.comp _ _ _
      ((n : ℚ)⁻¹ ⊗ₜ[ℤ] q) ((n : ℚ)⁻¹ ⊗ₜ[ℤ] r) = _
    rw [Rationalization.comp_tmul, hqr, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    have hnn : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hc : (n * n : ℕ) • ((n : ℚ)⁻¹ * (n : ℚ)⁻¹) = 1 := by
      rw [nsmul_eq_mul]
      push_cast
      field_simp
    rw [hc]
    rfl

theorem squareReverseIso_tate_apply
    (T : Over S) (n : ℕ) (hn : 0 < n) (q : A ⟶ B) (r : B ⟶ A)
    (hqr : q ≫ r = (n * n) • 𝟙 A) (hrq : r ≫ q = (n * n) • 𝟙 B)
    (x : Full B T) :
    rationalHomMap T (fun _ => True) (squareReverseIso n hn q r hqr hrq).hom
        (GroupScheme.Tate.toRational B.toGrp T (fun _ => True) x) =
      (n : ℚ)⁻¹ • GroupScheme.Tate.toRational A.toGrp T (fun _ => True)
        (map T (fun _ => True) r x) := rfl

/-- The normalized integral-image equality implies the prescribed rational-image equality. -/
theorem squareReverseIso_image_iff
    (T : Over S) (n : ℕ) (hn : 0 < n) (q : A ⟶ B) (r : B ⟶ A)
    (hqr : q ≫ r = (n * n) • 𝟙 A) (hrq : r ≫ q = (n * n) • 𝟙 B)
    (L : AddSubgroup (RationalFull A T))
    (hupper : ∀ w ∈ L, ∃ x : Full A T,
      GroupScheme.Tate.toRational A.toGrp T (fun _ => True) x = n • w)
    (himage : ∀ x : Full A T, (∃ y : Full B T, map T (fun _ => True) r y = x) ↔
      x ∈ GroupScheme.Tate.normalizedIntegralSubgroup A.toGrp T n L)
    (w : RationalFull A T) :
    w ∈ L ↔ ∃ x : Full B T,
      rationalHomMap T (fun _ => True) (squareReverseIso n hn q r hqr hrq).hom
        (GroupScheme.Tate.toRational B.toGrp T (fun _ => True) x) = w := by
  have hnn : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc (z : RationalFull A T) : (n : ℚ)⁻¹ • n • z = z := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hnn]
  constructor
  · intro hw
    obtain ⟨x, hx, hrat⟩ :=
      GroupScheme.Tate.exists_normalizedIntegralSubgroup_of_upper_bound
        A.toGrp T n L hupper w hw
    obtain ⟨y, hy⟩ := (himage x).mpr hx
    refine ⟨y, ?_⟩
    rw [squareReverseIso_tate_apply, hy, hrat, hc]
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz, hrat⟩ := (himage (map T (fun _ => True) r y)).mp ⟨y, rfl⟩
    rw [squareReverseIso_tate_apply, hrat, hc]
    exact hz

end Langlands.AbelianScheme.Tate
