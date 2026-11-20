import Langlands.Automorphic.OperatorRealization
import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.AdelicGLIwasawa
import Langlands.Representation.Whittaker.Algebraic

/-!
# Scalar sections for adelic block induction

Unipotent-invariant scalar functions with specified normalized Levi slices have a
compact picture. Restriction and extension use the actual Iwasawa decomposition
and retain the constructed positive half character.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight
open Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local notation "K" => (standardCompact F n)
local notation "M" => FullLevi F B
local notation "P" => Full F B
local notation "U" => B.unipotentRadical (Adeles F)
local notation "μ" => B.leviProjection (Adeles F)
local notation "j" => B.leviEmbedding (Adeles F)

/-- Each actual adelic matrix has a factorization in the given block parabolic and
the standard compact subgroup. -/
theorem exists_parabolic_mul_standardCompact (g : AdelicGL F n) :
    ∃ (p : P) (k : K), g = p.val * k.val := by
  obtain ⟨p, k, h, hp, hk⟩ := exists_isStandardIwasawaFactorization F n g
  exact ⟨⟨p, B.mem_parabolic_of_isUpperTriangular p
    ((mem_upperTriangularSubgroup_iff p).mp hp)⟩, ⟨k, hk⟩, h⟩

/-- The normalized Levi slice of a scalar function at a compact matrix. -/
def normalizedSlice (f : AdelicGL F n → ℂ) (k : K) (m : M) : ℂ :=
  (leviHalfCharacter F B m : ℂ)⁻¹ * f (j m * k.val)

/-- Scalar functions on the actual adelic group, invariant under the left unipotent radical
and with normalized Levi slices in the specified coefficient space. -/
def ScalarSections (W : Submodule ℂ (M → ℂ)) : Submodule ℂ (AdelicGL F n → ℂ) where
  carrier := {f | (∀ (u : U) (g : AdelicGL F n), f (u.val.val * g) = f g) ∧
    ∀ k : K, normalizedSlice F B f k ∈ W}
  zero_mem' := ⟨fun _ _ => rfl, fun k => by
    rw [show normalizedSlice F B 0 k = 0 from funext fun _ => mul_zero _]
    exact W.zero_mem⟩
  add_mem' := by
    rintro f g ⟨hf, hfW⟩ ⟨hg, hgW⟩
    refine ⟨fun u x => by simp only [Pi.add_apply, hf u x, hg u x], fun k => ?_⟩
    have h : normalizedSlice F B (f + g) k =
        normalizedSlice F B f k + normalizedSlice F B g k := by
      funext m
      exact mul_add _ _ _
    rw [h]
    exact W.add_mem (hfW k) (hgW k)
  smul_mem' := by
    rintro c f ⟨hf, hfW⟩
    refine ⟨fun u x => by simp only [Pi.smul_apply, hf u x], fun k => ?_⟩
    have h : normalizedSlice F B (c • f) k = c • normalizedSlice F B f k := by
      ext m
      simp only [normalizedSlice, Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [h]
    exact W.smul_mem c (hfW k)

/-- In the compact picture the scalar Levi slices obey covariance for the compact
elements of the actual parabolic. -/
def CompactSections (W : Submodule ℂ (M → ℂ)) : Submodule ℂ (K → M → ℂ) where
  carrier := {Φ | (∀ k, Φ k ∈ W) ∧
    ∀ (p : P) (hp : p.val ∈ standardCompact F n) (k : K) (m : M),
      Φ (⟨p.val, hp⟩ * k) m = (parabolicHalfCharacter F B p : ℂ) * Φ k (m * μ p)}
  zero_mem' := ⟨fun _ => W.zero_mem, fun _ _ _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hfW, hf⟩ ⟨hgW, hg⟩
    exact ⟨fun k => W.add_mem (hfW k) (hgW k), fun p hp k m => by
      simp only [Pi.add_apply, hf p hp k m, hg p hp k m, mul_add]⟩
  smul_mem' := by
    rintro c f ⟨hfW, hf⟩
    exact ⟨fun k => W.smul_mem c (hfW k), fun p hp k m => by
      simp only [Pi.smul_apply, smul_eq_mul, hf p hp k m, mul_left_comm]⟩

variable (W : Submodule ℂ (FullLevi F B → ℂ))

/-- The compact slices recover a scalar section on each actual parabolic–compact product. -/
theorem scalarSection_apply_mul (f : ScalarSections F B W) (p : P) (k : K) :
    f.val (p.val * k.val) =
      (parabolicHalfCharacter F B p : ℂ) * normalizedSlice F B f.val k (μ p) := by
  have h : (B.unipotentPart (Adeles F) p).val.val * j (μ p) = p.val :=
    congrArg Subtype.val ((B.decomposition (Adeles F)).left_inv p)
  calc
    f.val (p.val * k.val) = f.val ((B.unipotentPart (Adeles F) p).val.val * (j (μ p) * k.val)) := by
      rw [← mul_assoc, h]
    _ = f.val (j (μ p) * k.val) := f.property.1 _ _
    _ = _ := by
      change _ = (leviHalfCharacter F B (μ p) : ℂ) *
        ((leviHalfCharacter F B (μ p) : ℂ)⁻¹ * f.val (j (μ p) * k.val))
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

/-- Restriction to the normalized slices on the standard compact subgroup. -/
def restrict : ScalarSections F B W →ₗ[ℂ] CompactSections F B W where
  toFun f := ⟨normalizedSlice F B f.val, f.property.2, fun p hp k m => by
    calc
      normalizedSlice F B f.val (⟨p.val, hp⟩ * k) m =
          (leviHalfCharacter F B m : ℂ)⁻¹ *
            f.val ((B.leviInParabolic (Adeles F) m * p).val * k.val) := by
        simp only [normalizedSlice, Subgroup.coe_mul, B.leviInParabolic_val, mul_assoc]
      _ = _ := by
        rw [scalarSection_apply_mul F B W]
        simp only [map_mul, parabolicHalfCharacter_section, B.leviProjection_section,
          Units.val_mul]
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]⟩
  map_add' f g := Subtype.ext (by
    funext k m
    exact mul_add _ _ _)
  map_smul' c f := Subtype.ext (by
    funext k m
    exact mul_left_comm _ _ _)

private theorem compactValue_eq (Φ : CompactSections F B W) {p q : P} {k l : K}
    (h : p.val * k.val = q.val * l.val) :
    (parabolicHalfCharacter F B p : ℂ) * Φ.val k (μ p) =
      (parabolicHalfCharacter F B q : ℂ) * Φ.val l (μ q) := by
  let a := q⁻¹ * p
  have hak : a.val * k.val = l.val := by
    change (q.val⁻¹ * p.val) * k.val = l.val
    rw [mul_assoc, h, inv_mul_cancel_left]
  have ha : a.val ∈ standardCompact F n := by
    rw [eq_mul_inv_of_mul_eq hak]
    exact (standardCompact F n).mul_mem l.property ((standardCompact F n).inv_mem k.property)
  have hl : (⟨a.val, ha⟩ : K) * k = l := Subtype.ext hak
  have hqa : q * a = p := mul_inv_cancel_left _ _
  have hma : μ q * μ a = μ p := ((μ).map_mul q a).symm.trans (congrArg (μ) hqa)
  have hhalf : (parabolicHalfCharacter F B q : ℂ) * (parabolicHalfCharacter F B a : ℂ) =
      (parabolicHalfCharacter F B p : ℂ) := by
    rw [← Units.val_mul, ← map_mul, hqa]
  rw [← hl, Φ.property.2 a ha k (μ q), ← mul_assoc, hhalf, hma]

private def extension (Φ : CompactSections F B W) (g : AdelicGL F n) : ℂ :=
  let h := exists_parabolic_mul_standardCompact F B g
  let p := h.choose
  let k := h.choose_spec.choose
  (parabolicHalfCharacter F B p : ℂ) * Φ.val k (μ p)

private theorem extension_apply (Φ : CompactSections F B W) (p : P) (k : K) :
    extension F B W Φ (p.val * k.val) =
      (parabolicHalfCharacter F B p : ℂ) * Φ.val k (μ p) := by
  let h := exists_parabolic_mul_standardCompact F B (p.val * k.val)
  exact compactValue_eq F B W Φ h.choose_spec.choose_spec.symm

/-- Iwasawa extension from the compact picture to the actual adelic group. -/
def extend (Φ : CompactSections F B W) : ScalarSections F B W :=
  ⟨extension F B W Φ, ⟨fun u g => by
    obtain ⟨p, k, rfl⟩ := exists_parabolic_mul_standardCompact F B g
    change extension F B W Φ (u.val.val * (p.val * k.val)) =
      extension F B W Φ (p.val * k.val)
    rw [← mul_assoc, ← Subgroup.coe_mul, extension_apply, extension_apply,
      map_mul, map_mul, parabolicHalfCharacter_unipotent, one_mul]
    have hu : μ u.val = 1 := u.property
    rw [hu, one_mul], fun k => by
    have hs : normalizedSlice F B (extension F B W Φ) k = Φ.val k := by
      funext m
      change (leviHalfCharacter F B m : ℂ)⁻¹ *
        extension F B W Φ ((B.leviInParabolic (Adeles F) m).val * k.val) = _
      rw [extension_apply, parabolicHalfCharacter_section, B.leviProjection_section,
        ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    rw [hs]
    exact Φ.property.1 k⟩⟩

@[simp]
theorem extend_apply_mul (Φ : CompactSections F B W) (p : P) (k : K) :
    (extend F B W Φ).val (p.val * k.val) =
      (parabolicHalfCharacter F B p : ℂ) * Φ.val k (μ p) :=
  extension_apply F B W Φ p k

/-- The scalar section and compact pictures are linearly equivalent. -/
def compactPictureEquiv : ScalarSections F B W ≃ₗ[ℂ] CompactSections F B W where
  toLinearMap := restrict F B W
  invFun := extend F B W
  left_inv f := by
    apply Subtype.ext
    funext g
    obtain ⟨p, k, rfl⟩ := exists_parabolic_mul_standardCompact F B g
    rw [extend_apply_mul]
    exact (scalarSection_apply_mul F B W f p k).symm
  right_inv Φ := by
    apply Subtype.ext
    funext k m
    change (leviHalfCharacter F B m : ℂ)⁻¹ *
      (extend F B W Φ).val ((B.leviInParabolic (Adeles F) m).val * k.val) = _
    rw [extend_apply_mul, parabolicHalfCharacter_section, B.leviProjection_section,
      ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

/-- Scalar sections are stable under actual right translations by the standard compact group. -/
def ScalarSections.compactSubrepresentation :
    Subrepresentation ((Whittaker.rightTranslation ℂ (AdelicGL F n)).comp
      (standardCompact F n).subtype) where
  toSubmodule := ScalarSections F B W
  apply_mem_toSubmodule k f hf := ⟨fun u g => by
    change f ((u.val.val * g) * k.val) = f (g * k.val)
    exact (congrArg f (mul_assoc _ _ _)).trans (hf.1 _ _), fun l => by
    convert hf.2 (l * k) using 1
    funext m
    change (leviHalfCharacter F B m : ℂ)⁻¹ * f ((j m * l.val) * k.val) =
      (leviHalfCharacter F B m : ℂ)⁻¹ * f (j m * (l.val * k.val))
    rw [mul_assoc]⟩

section ActualCoefficients

open Langlands.Automorphic

variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

/-- Evaluation of a pure block coefficient on the actual adelic Levi. -/
def blockCoefficient (f : ∀ i, (S i).Space) (m : M) : ℂ :=
  ∏ i, ContinuousRationalFunctions.evaluate F (B.size i) ((S i).toContinuous (f i)) (m i)

/-- Finite linear combinations of products of the actual block coefficients. -/
def coefficientValues : Submodule ℂ (M → ℂ) :=
  Submodule.span ℂ (Set.range (blockCoefficient F B S))

/-- The geometric scalar carrier obtained from the supplied block realizations. -/
abbrev RealizedSections := ScalarSections F B (coefficientValues F B S)

/-- The realized coefficient space is left invariant under the rational Levi group. -/
theorem coefficientValues_rational {φ : M → ℂ} (hφ : φ ∈ coefficientValues F B S)
    (γ : B.Levi F) (m : M) :
    φ (rationalLevi F B γ * m) = φ m := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, rfl⟩ := h
    refine Finset.prod_congr rfl fun i _ => ?_
    exact ContinuousRationalFunctions.evaluate_rational F (B.size i)
      ((S i).toContinuous (f i)) (γ i) (m i)
  | zero => rfl
  | add φ ψ _ _ hφ hψ => simp only [Pi.add_apply, hφ, hψ]
  | smul c φ _ hφ => simp only [Pi.smul_apply, hφ]

/-- The scalar sections from actual block realizations descend through the rational
parabolic action on the left. -/
theorem realizedSection_rational (f : RealizedSections F B S) (γ : Rational F B)
    (g : AdelicGL F n) :
    f.val ((AdelicBlockParabolic.rational F B γ).val * g) = f.val g := by
  obtain ⟨p, k, rfl⟩ := exists_parabolic_mul_standardCompact F B g
  rw [← mul_assoc, ← Subgroup.coe_mul, scalarSection_apply_mul, scalarSection_apply_mul,
    map_mul, parabolicHalfCharacter_rational, one_mul, map_mul, leviProjection_rational]
  rw [coefficientValues_rational F B S (f.property.2 k)]

end ActualCoefficients

end Langlands.Global.AdelicBlockScalarSections
