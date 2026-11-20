import Langlands.Geometry.FormalGroup.FrobeniusTorsionPairing
import Langlands.Geometry.FormalGroup.PolarizedRationalSectionIso
import Langlands.Geometry.FormalGroup.ScalarIsogenyTensorInverse

/-! # Rational similitude of polarized relative Frobenius -/

noncomputable section

universe w

namespace Langlands.FormalGroup.ModuleLaw.PolarizedOrderModule

open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry Langlands.GroupScheme Langlands.Shimura
open scoped CategoryTheory.MonObj CategoryTheory.Obj

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option backward.isDefEq.respectTransparency false

section Pairing

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}
variable {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}
variable {P : TorsionPrincipalPolarization hM} {Q : TorsionPrincipalPolarization hN}

private theorem scaledDual_pairing {f : Hom M N} {g : Hom N M} (k l : ℕ)
    (hf : f.IsTorsionSimilitude P Q (k : O)) (hfg : f.comp g = N.scalarHom (l : O)) :
    ((M.scalarHom (k : O)).comp g).IsTorsionSimilitude Q P ((l * l * k : ℕ) : O) := by
  intro n T x y
  let G := (g.scalarTorsionSchemeMap hN hM n).toMul.hom.hom
  let F := (f.scalarTorsionSchemeMap hM hN n).toMul.hom.hom
  let A := P.toTorsionCartierDuality
  let B := Q.toTorsionCartierDuality
  have hF (z : T ⟶ (hN.torsionSchemeInclusions.obj n).X) : (z ≫ G) ≫ F = z ^ l := by
    calc
      (z ≫ G) ≫ F = z ≫ ((f.comp g).scalarTorsionSchemeMap hN hN n).toMul.hom.hom := by
        rw [Hom.scalarTorsionSchemeMap_comp _ _ _ _ _]
        exact Category.assoc _ _ _
      _ = z ^ l := by rw [hfg, scalarTorsionSchemeMap_natCast_points]
  have hG (z : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
      z ≫ (((M.scalarHom (k : O)).comp g).scalarTorsionSchemeMap hN hM n).toMul.hom.hom =
        (z ≫ G) ^ k := by
    rw [Hom.scalarTorsionSchemeMap_comp hN hM hM]
    change z ≫ G ≫ ((M.scalarHom (k : O)).scalarTorsionSchemeMap hM hM n).toMul.hom.hom = _
    rw [← Category.assoc, scalarTorsionSchemeMap_natCast_points]
  have h := hf n T (x ≫ G) (y ≫ G)
  change B.pairing n ((x ≫ G) ≫ F) ((y ≫ G) ≫ F) =
    A.pairing n ((x ≫ G) ≫ ((M.scalarHom (k : O)).scalarTorsionSchemeMap hM hM n).toMul.hom.hom)
      (y ≫ G) at h
  rw [hF, hF, scalarTorsionSchemeMap_natCast_points] at h
  let rightA : (T ⟶ (hM.torsionSchemeInclusions.obj n).X) →* (T ⟶ (Gm _).X) :=
    MonoidHom.mk' (A.pairing n ((x ≫ G) ^ k))
      (A.pairing_mul_right n ((x ≫ G) ^ k))
  let rightB : (T ⟶ (hN.torsionSchemeInclusions.obj n).X) →* (T ⟶ (Gm _).X) :=
    MonoidHom.mk' (B.pairing n (x ^ l)) (B.pairing_mul_right n (x ^ l))
  let leftB : (T ⟶ (hN.torsionSchemeInclusions.obj n).X) →* (T ⟶ (Gm _).X) :=
    MonoidHom.mk' (fun z => B.pairing n z y) (fun z z' => B.pairing_mul_left n z z' y)
  rw [hG, hG, scalarTorsionSchemeMap_natCast_points]
  calc
    A.pairing n ((x ≫ G) ^ k) ((y ≫ G) ^ k) =
        (A.pairing n ((x ≫ G) ^ k) (y ≫ G)) ^ k := map_pow rightA (y ≫ G) k
    _ = (B.pairing n (x ^ l) (y ^ l)) ^ k := congrArg (fun z => z ^ k) h.symm
    _ = ((B.pairing n (x ^ l) y) ^ l) ^ k := congrArg (fun z => z ^ k) (map_pow rightB y l)
    _ = B.pairing n (x ^ (l * l * k)) y := by
      change ((leftB (x ^ l)) ^ l) ^ k = leftB (x ^ (l * l * k))
      rw [← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_assoc]

end Pairing

/-- The rational multiplier of the `m`-fold relative Frobenius. -/
def frobeniusMultiplier (p : ℕ) [Fact p.Prime] (m : ℕ) : ℚ_[p]ˣ :=
  Units.mk0 ((p : ℚ_[p]) ^ m) (pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

@[simp]
theorem coe_frobeniusMultiplier (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (frobeniusMultiplier p m : ℚ_[p]) = (p : ℚ_[p]) ^ m := rfl

@[simp]
theorem coe_frobeniusMultiplier_inv (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (↑((frobeniusMultiplier p m)⁻¹) : ℚ_[p]) = ((p : ℚ_[p]) ^ m)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, coe_frobeniusMultiplier]

variable {p : ℕ} [Fact p.Prime]
variable {A : Type w} [Ring A] [Algebra ℤ_[p] A] {star : AlgebraInvolution ℤ_[p] A}
variable {R : Type} [CommRing R] [Algebra ℤ_[p] R]
variable (X : PolarizedOrderModule A star R (p : ℤ_[p]))
variable [ExpChar R p] (m : ℕ) (θ : R →ₐ[ℤ_[p]] R)
variable (hθ : θ.toRingHom = iterateFrobenius R p m)

local notation "frob" => X.order.frobeniusHom p m θ hθ

set_option maxHeartbeats 1200000 in
private def frobeniusSectionIso (hf : (frob).val.IsIsogeny) :
    {e : RationalSectionIso ℚ_[p] X.law (X.map θ).law ⊤ //
      e.hom = RationalSection.ofHom (frob).val ⊤ ∧
        RationalSection.HasPadicTorsionSimilitude p X.polarization (X.map θ).polarization e.hom
          (frobeniusMultiplier p m) ∧
        RationalSection.HasPadicTorsionSimilitude p (X.map θ).polarization X.polarization e.inv
          (frobeniusMultiplier p m)⁻¹} := by
  let Y := X.map θ
  let f : Hom X.law Y.law := (frob).val
  let a : ℤ_[p] := p
  let b : ℚ_[p] := p
  have hb : b ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hm : f.IsTorsionSimilitude X.polarization Y.polarization (a ^ m) :=
    frobeniusHom_isTorsionSimilitude X.divisible m θ hθ X.polarization
  have hf' : f.IsIsogeny := hf
  let duals := hf'.exists_dual X.divisible Y.divisible
  let d := duals.choose
  let dual := duals.choose_spec d le_rfl
  let g := dual.choose
  have hg : g.IsIsogeny := dual.choose_spec.1
  have hgf : g.comp f = X.law.scalarHom (a ^ d) := dual.choose_spec.2.1
  have hfg : f.comp g = Y.law.scalarHom (a ^ d) := dual.choose_spec.2.2
  have hbmap : algebraMap ℤ_[p] ℚ_[p] a = b := map_natCast _ _
  let e : QuasiIsogeny ℚ_[p] X.law Y.law := {
    hom := RationalHom.ofHom f
    inv := (b ^ d)⁻¹ • RationalHom.ofHom g
    inv_hom := by
      rw [RationalHom.smul_comp, ← RationalHom.ofHom_comp, hgf,
        RationalHom.ofHom_scalarHom, map_pow, hbmap, inv_smul_smul₀ (pow_ne_zero d hb)]
    hom_inv := by
      rw [RationalHom.comp_smul, ← RationalHom.ofHom_comp, hfg,
        RationalHom.ofHom_scalarHom, map_pow, hbmap, inv_smul_smul₀ (pow_ne_zero d hb)] }
  let g' := (X.law.scalarHom (a ^ m)).comp g
  have hg' : g'.IsIsogeny := (X.divisible.scalarPower_isIsogeny m).comp_of_finiteKernelComposition
    (Hom.finiteKernelCompositionStatement _ _ _) hg
  have hg'm : g'.IsTorsionSimilitude Y.polarization X.polarization (a ^ (2 * d + m)) := by
    have eq : f.comp g = Y.law.scalarHom ((p ^ d : ℕ) : ℤ_[p]) := by
      simpa only [Nat.cast_pow] using hfg
    have hp := scaledDual_pairing (p ^ m) (p ^ d)
      (show f.IsTorsionSimilitude X.polarization Y.polarization ((p ^ m : ℕ) : ℤ_[p]) by
        simpa only [Nat.cast_pow] using hm) eq
    simpa only [Nat.cast_mul, Nat.cast_pow, pow_add, two_mul, mul_assoc] using hp
  have hrep : (algebraMap ℤ_[p] ℚ_[p] a) ^ (d + m) • e.inv = RationalHom.ofHom g' := by
    change (algebraMap ℤ_[p] ℚ_[p] a) ^ (d + m) • ((b ^ d)⁻¹ • RationalHom.ofHom g) =
      RationalHom.ofHom ((X.law.scalarHom (a ^ m)).comp g)
    rw [hbmap, RationalHom.ofHom_comp, RationalHom.ofHom_scalarHom, map_pow, hbmap,
      RationalHom.smul_comp, RationalHom.id_comp, pow_add, mul_comm (b ^ d),
      smul_smul, mul_inv_cancel_right₀ (pow_ne_zero d hb)]
  refine ⟨RationalSectionIso.ofQuasiIsogeny e ⊤, RationalSection.ofGlobalOn_ofHom ⊤ f, ?_, ?_⟩
  · exact RationalSection.HasLocalTorsionSimilitude.ofGlobalOn f hf' (a ^ m)
      (by rw [map_pow, hbmap]; rfl) (by simpa only [Algebra.algebraMap_self_apply] using hm)
  · apply RationalSection.HasLocalTorsionSimilitude.ofGlobalPresentationOn
      (p := a) (d + m) g' hg'
      (by simpa only [Algebra.algebraMap_self_apply] using hrep) (a ^ (2 * d + m))
    · change algebraMap ℤ_[p] ℚ_[p] (a ^ (2 * d + m)) =
        (algebraMap ℤ_[p] ℚ_[p] a) ^ (2 * (d + m)) * (b ^ m)⁻¹
      rw [map_pow, hbmap, show 2 * (d + m) = (2 * d + m) + m by omega, pow_add b (2 * d + m) m,
        mul_inv_cancel_right₀ (pow_ne_zero m hb)]
    · simpa only [Algebra.algebraMap_self_apply] using hg'm

/-- Relative Frobenius, when it is an isogeny, gives a full-order rational
polarized similitude from the frame to its coefficient Frobenius twist. -/
def frobeniusRationalSimilitude (hf : (frob).val.IsIsogeny) :
    RationalSimilitudeIso X (X.map θ) ⊤ where
  sectionIso := (frobeniusSectionIso X m θ hθ hf).val
  orderLinear := (frobeniusSectionIso X m θ hθ hf).property.1.symm ▸
    RationalSection.IsOrderLinear.ofHom frob ⊤
  similitude := ⟨frobeniusMultiplier p m, (frobeniusSectionIso X m θ hθ hf).property.2⟩

@[simp]
theorem frobeniusRationalSimilitude_hom (hf : (frob).val.IsIsogeny) :
    (X.frobeniusRationalSimilitude m θ hθ hf).sectionIso.hom =
      RationalSection.ofHom (frob).val ⊤ :=
  (frobeniusSectionIso X m θ hθ hf).property.1

/-- The forward and inverse sections satisfy the actual torsion equations with the
specified reciprocal rational multipliers. -/
theorem frobeniusRationalSimilitude_hasMultipliers (hf : (frob).val.IsIsogeny) :
    RationalSection.HasPadicTorsionSimilitude p X.polarization (X.map θ).polarization
        (X.frobeniusRationalSimilitude m θ hθ hf).sectionIso.hom (frobeniusMultiplier p m) ∧
      RationalSection.HasPadicTorsionSimilitude p (X.map θ).polarization X.polarization
        (X.frobeniusRationalSimilitude m θ hθ hf).sectionIso.inv (frobeniusMultiplier p m)⁻¹ :=
  (frobeniusSectionIso X m θ hθ hf).property.2

end Langlands.FormalGroup.ModuleLaw.PolarizedOrderModule
