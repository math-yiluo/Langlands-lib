import Langlands.AlgebraicGeometry.Modules.AffineBaseSections
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Actual kernels of affine quotient base changes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel

variable {B' B : Type u} [CommRing B'] [CommRing B]
  (φ : B' →+* B) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B'))

/-- The base ring acts on sections through the actual structure morphism. -/
abbrev sectionHom (U : X.Opens) : B' →+* Γ(X, U) :=
  Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient.baseSectionHom f U

/-- The actual affine-section kernel of a base-changed quotient is its extended ideal. -/
lemma affine_ker (hφ : Function.Surjective φ) (U : X.Opens) (hU : IsAffineOpen U) :
    RingHom.ker ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app U).hom =
      (RingHom.ker φ).map (sectionHom f U) := by
  let j := Spec.map (CommRingCat.ofHom φ)
  let i := pullback.fst f j
  let p := pullback.snd f j
  have H := IsPullback.of_hasPullback f j
  have hUY : i ⁻¹ᵁ U = i ⁻¹ᵁ U ⊓ p ⁻¹ᵁ ⊤ := by simp
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY
    (isAffineOpen_top (Spec (CommRingCat.of B')))
    (isAffineOpen_top (Spec (CommRingCat.of B))) hU
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top hUY).mp h1
  have hleg : j.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of B')).hom ≫ CommRingCat.ofHom φ ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    change (Spec.map (CommRingCat.ofHom φ)).appTop = _
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hg : Function.Surjective (j.appLE ⊤ ⊤ le_top).hom := by
    rw [hleg]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2.comp
      (hφ.comp (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of B')).hom).2)
  have hker :=
    P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.CommRingCat.ker_eq_map_ker_of_isPushout
      h2 hg
  rw [Scheme.Hom.appLE_eq_app] at hker
  rw [hker, hleg]
  have hbase : RingHom.ker
      ((Scheme.ΓSpecIso (CommRingCat.of B')).hom ≫ CommRingCat.ofHom φ ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv).hom =
      (RingHom.ker φ).map (Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom := by
    change RingHom.ker
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.comp
        (φ.comp (Scheme.ΓSpecIso (CommRingCat.of B')).hom.hom)) = _
    rw [RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1, ← RingHom.comap_ker]
    exact (Ideal.map_symm
      (Scheme.ΓSpecIso (CommRingCat.of B')).commRingCatIsoToRingEquiv).symm
  rw [hbase, Ideal.map_map]
  rfl

/-- A surjective base quotient induces a closed immersion on the actual fibre product. -/
lemma isClosedImmersion (hφ : Function.Surjective φ) :
    IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  infer_instance

/-- Vanishing powers of a quotient ideal stay zero in the actual base-change kernel. -/
lemma ker_pow_eq_bot (hφ : Function.Surjective φ) (n : ℕ)
    (hn : (RingHom.ker φ) ^ n = ⊥) :
    (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).ker ^ n = ⊥ := by
  let := isClosedImmersion φ f hφ
  apply Scheme.IdealSheafData.ext
  funext U
  change (((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).ker).ideal U) ^ n = ⊥
  rw [Scheme.Hom.ker_apply, affine_ker φ f hφ U.1 U.2,
    ← Ideal.map_pow, hn, Ideal.map_bot]

/-- A maximal-ideal-annihilated elementary kernel is square zero after base change. -/
lemma ker_sq [IsLocalRing B'] [Nontrivial B] (hφ : Function.Surjective φ)
    (h : IsLocalRing.maximalIdeal B' * RingHom.ker φ = ⊥) :
    (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).ker ^ 2 = ⊥ := by
  apply ker_pow_eq_bot φ f hφ 2
  rw [pow_two]
  exact le_antisymm
    ((mul_le_mul' (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)) le_rfl).trans_eq h)
    bot_le

end Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel
