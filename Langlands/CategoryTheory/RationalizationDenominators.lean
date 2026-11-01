import Langlands.CategoryTheory.Rationalization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Module.LocalizedModule.Int

/-! # Integral representatives of rationalized morphisms -/

noncomputable section

open CategoryTheory

universe v u

namespace Langlands.Rationalization

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The existing integral inclusion on Hom groups is localization at nonzero integers. -/
instance ofHom_isLocalizedModule (X Y : C) :
    IsLocalizedModule (nonZeroDivisors ℤ) (ofHom (X := X) (Y := Y)) :=
  IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ

/-- A rational morphism has an integral representative after multiplication by a nonzero integer. -/
theorem exists_integral_multiple {X Y : C} (f : Hom X Y) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ g : X ⟶ Y, ofHom g = n • f := by
  obtain ⟨n, g, hg⟩ := IsLocalizedModule.exists_integer_multiple
    (nonZeroDivisors ℤ) (ofHom (X := X) (Y := Y)) f
  exact ⟨n, mem_nonZeroDivisors_iff_ne_zero.mp n.prop, g, hg⟩

/-- A finite family of rational morphisms has one common nonzero integral denominator. -/
theorem exists_common_integral_multiple {X Y : C} {ι : Type*} [Finite ι]
    (f : ι → Hom X Y) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ g : ι → (X ⟶ Y), ∀ i, ofHom (g i) = n • f i := by
  obtain ⟨n, hn⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (ofHom (X := X) (Y := Y)) f
  choose g hg using hn
  exact ⟨n, mem_nonZeroDivisors_iff_ne_zero.mp n.prop, g, hg⟩

/-- Rational equality of integral maps is detected by a nonzero integer multiple. -/
theorem ofHom_eq_iff_exists_zsmul_eq {X Y : C} (f g : X ⟶ Y) :
    ofHom f = ofHom g ↔ ∃ n : ℤ, n ≠ 0 ∧ n • f = n • g := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
      (ofHom (X := X) (Y := Y))).mp h
    exact ⟨n, mem_nonZeroDivisors_iff_ne_zero.mp n.prop, hn⟩
  · rintro ⟨n, hn, h⟩
    exact (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
      (ofHom (X := X) (Y := Y))).mpr ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, h⟩

@[simp] theorem ofHom_id (X : C) : ofHom (𝟙 X) = 𝟙 (of X) := rfl

@[simp] theorem ofHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofHom (f ≫ g) = comp X Y Z (ofHom f) (ofHom g) :=
  (inclusion (C := C)).map_comp f g

/-- Integral maps representing a rational isomorphism, with exact integral composite identities. -/
structure IntegralIsoData {X Y : C} (e : of X ≅ of Y) where
  homDenom : ℤ
  invDenom : ℤ
  homDenom_ne_zero : homDenom ≠ 0
  invDenom_ne_zero : invDenom ≠ 0
  hom : X ⟶ Y
  inv : Y ⟶ X
  ofHom_hom : ofHom hom = homDenom • e.hom
  ofHom_inv : ofHom inv = invDenom • e.inv
  hom_inv : hom ≫ inv = (homDenom * invDenom) • 𝟙 X
  inv_hom : inv ≫ hom = (homDenom * invDenom) • 𝟙 Y

/-- Every rational isomorphism admits integral representatives with exact composite identities. -/
theorem nonempty_integralIsoData {X Y : C} (e : of X ≅ of Y) :
    Nonempty (IntegralIsoData e) := by
  obtain ⟨a, ha, f, hf⟩ := exists_integral_multiple e.hom
  obtain ⟨b, hb, g, hg⟩ := exists_integral_multiple e.inv
  have hfg : ofHom (f ≫ g) = ofHom ((a * b) • 𝟙 X) := by
    rw [ofHom_comp, hf, hg]
    change compLinear X Y X (a • e.hom) (b • e.inv) = _
    rw [map_zsmul (compLinear X Y X) a e.hom, LinearMap.smul_apply, map_zsmul]
    change a • (b • (e.hom ≫ e.inv)) = _
    rw [e.hom_inv_id]
    simp only [map_smul, ofHom_id, smul_smul]
  have hgf : ofHom (g ≫ f) = ofHom ((a * b) • 𝟙 Y) := by
    rw [ofHom_comp, hg, hf]
    change compLinear Y X Y (b • e.inv) (a • e.hom) = _
    rw [map_zsmul (compLinear Y X Y) b e.inv, LinearMap.smul_apply, map_zsmul]
    change b • (a • (e.inv ≫ e.hom)) = _
    rw [e.inv_hom_id]
    simp only [map_smul, ofHom_id, smul_smul, mul_comm b a]
  obtain ⟨k, hk, hkeq⟩ := (ofHom_eq_iff_exists_zsmul_eq _ _).mp hfg
  obtain ⟨l, hl, hleq⟩ := (ofHom_eq_iff_exists_zsmul_eq _ _).mp hgf
  have hfg' : (k * l) • (f ≫ g) = (k * l) • ((a * b) • 𝟙 X) := by
    simpa only [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t => l • t) hkeq
  have hgf' : (k * l) • (g ≫ f) = (k * l) • ((a * b) • 𝟙 Y) := by
    simpa only [smul_smul, mul_assoc] using congrArg (fun t => k • t) hleq
  refine ⟨{
    homDenom := (k * l) * a
    invDenom := b
    homDenom_ne_zero := mul_ne_zero (mul_ne_zero hk hl) ha
    invDenom_ne_zero := hb
    hom := (k * l) • f
    inv := g
    ofHom_hom := ?_
    ofHom_inv := hg
    hom_inv := ?_
    inv_hom := ?_ }⟩
  · rw [map_smul, hf, smul_smul]
  · rw [Preadditive.zsmul_comp, hfg']
    simp only [smul_smul, mul_assoc]
  · rw [Preadditive.comp_zsmul, hgf']
    simp only [smul_smul, mul_assoc]

/-- A choice of integral representatives for a rational isomorphism. -/
def integralIsoData {X Y : C} (e : of X ≅ of Y) : IntegralIsoData e :=
  Classical.choice (nonempty_integralIsoData e)

end Langlands.Rationalization
