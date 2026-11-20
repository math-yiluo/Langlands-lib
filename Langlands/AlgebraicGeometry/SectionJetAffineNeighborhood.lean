import Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Langlands.RingTheory.Smooth.SectionJetFiniteDetection
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite-jet detection near a section on affine charts -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

/-- Order `n` detects vanishing near the changed section if, on every affine
test, containment in the extended section ideal to power `n + 1` forces
vanishing on a neighborhood of that section. -/
def DetectsVanishingNearSectionAffine {S X : Scheme.{u}} (f : X ⟶ S)
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) (J : X.IdealSheafData) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) [IsAffine T] (b : T ⟶ S),
    let p := pullback.snd b f
    let eT := pullback.lift (𝟙 T) (b ≫ e)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
    J.comap p ≤ (e.ker ^ (n + 1)).comap p →
    ∃ W : (pullback b f).Opens, Set.range eT ⊆ W ∧ J ≤ (W.ι ≫ p).ker

set_option maxHeartbeats 500000 in
/-- If a finitely generated ideal vanishes on a sufficiently large section jet
after affine base change, it vanishes on an open containing the changed section. -/
theorem exists_order_of_vanishing_near_section_affine
    {S X : Scheme.{u}} [IsAffine S] [IsAffine X] (f : X ⟶ S) [Smooth f]
    (e : S ⟶ X) (he : e ≫ f = 𝟙 S) (J : X.IdealSheafData)
    (hJ : (J.ideal ⟨⊤, isAffineOpen_top X⟩).FG) :
    ∃ n : ℕ, DetectsVanishingNearSectionAffine f e he J n := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let ε : Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(S, ⊤) :=
    { toRingHom := e.appTop.hom
      commutes' := fun r => by
        have hc := congrArg (fun h : S ⟶ S => h.appTop) he
        rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hc
        exact ConcreteCategory.congr_hom hc r }
  let : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.appTop (P := @Smooth) f inferInstance
  let J₀ := J.ideal ⟨⊤, isAffineOpen_top X⟩
  obtain ⟨n, hn⟩ := Algebra.SectionJet.exists_order_of_finite_ideal_vanishing_near_section ε J₀ hJ
  refine ⟨n, fun T _ b => ?_⟩
  dsimp only
  intro hJet
  let Y := pullback b f
  let p : Y ⟶ X := pullback.snd b f
  let eT : T ⟶ Y := pullback.lift (𝟙 T) (b ≫ e)
    (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := b.appTop.hom.toAlgebra
  let c := AffineCoverCoefficientTensors.overlapTensorEquiv b f
  let inc := (Algebra.TensorProduct.includeRight :
    Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X, ⊤)).toRingHom
  have hInc : c.toRingHom.comp inc = p.appTop.hom := by
    ext x
    exact AffineCoverCoefficientTensors.overlapTensorEquiv_one_tmul b f x
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let V : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  have hApp : p.appLE (⊤ : X.Opens) (⊤ : Y.Opens) (by simp) = p.appTop := by
    rw [Scheme.Hom.appLE]
    change p.appTop ≫ Y.presheaf.map (𝟙 (op (⊤ : Y.Opens))) = p.appTop
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hComap (I : X.IdealSheafData) :
      (I.comap p).ideal V = (I.ideal U).map p.appTop.hom := by
    rw [Scheme.IdealSheafData.ideal_comap_of_le I p U V (by simp [U, V])]
    change (I.ideal U).map (p.appLE (⊤ : X.Opens) (⊤ : Y.Opens) (by simp)).hom = _
    rw [hApp]
  have hTop := hJet V
  change (J.comap p).ideal V ≤ ((e.ker ^ (n + 1)).comap p).ideal V at hTop
  rw [hComap, hComap, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.Hom.ker_apply] at hTop
  change J₀.map p.appTop.hom ≤ (RingHom.ker ε ^ (n + 1)).map p.appTop.hom at hTop
  have hVan (x : Γ(X, ⊤)) (hx : x ∈ J₀) :
      (1 ⊗ₜ[Γ(S, ⊤)] Ideal.Quotient.mk _ x :
        Γ(T, ⊤) ⊗[Γ(S, ⊤)] Algebra.SectionJet.Quotient ε n) = 0 := by
    apply (Algebra.SectionJet.baseChangeEquiv ε Γ(T, ⊤) n).injective
    rw [Algebra.SectionJet.baseChangeEquiv_tmul_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      Algebra.SectionJet.ker_baseChangeAugmentation, ← Ideal.map_pow]
    apply (Ideal.apply_mem_of_equiv_iff (f := c)).mp
    change c.toRingHom (inc x) ∈ ((RingHom.ker ε ^ (n + 1)).map inc).map c.toRingHom
    rw [Ideal.map_map, hInc, ← RingHom.comp_apply, hInc]
    exact hTop (Ideal.mem_map_of_mem _ hx)
  obtain ⟨r, hr, hrJ⟩ := hn Γ(T, ⊤) hVan
  have hLeft : (pullback.fst b f).appTop ≫ eT.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.id_appTop]
  have hRight : p.appTop ≫ eT.appTop = e.appTop ≫ b.appTop := by
    rw [← Scheme.Hom.comp_appTop, pullback.lift_snd, Scheme.Hom.comp_appTop]
  have hAug (z : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X, ⊤)) :
      eT.appTop (c z) = Algebra.SectionJet.baseChangeAugmentation ε Γ(T, ⊤) z := by
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      change eT.appTop (AffineCoverCoefficientTensors.overlapTensorEquiv b f
        (t ⊗ₜ[Γ(S, ⊤)] x)) = _
      rw [AffineCoverCoefficientTensors.overlapTensorEquiv_tmul, map_mul,
        Algebra.SectionJet.baseChangeAugmentation_tmul]
      exact congrArg₂ (· * ·) (ConcreteCategory.congr_hom hLeft t)
        (ConcreteCategory.congr_hom hRight x)
    | add x y hx hy => simp only [map_add, hx, hy]
  let W := Y.basicOpen (c r)
  refine ⟨W, ?_, Scheme.IdealSheafData.le_of_isAffine ?_⟩
  · rintro _ ⟨t, rfl⟩
    change t ∈ eT ⁻¹ᵁ Y.basicOpen (c r)
    rw [Scheme.preimage_basicOpen_top, hAug, hr]
    simp
  · let : IsAffine W.toScheme := (isAffineOpen_top Y).basicOpen (c r)
    rw [Scheme.Hom.ker_apply]
    intro x hx
    change (W.ι ≫ p).appTop x = 0
    have hrx : c r * p.appTop x = 0 := by
      have hx' : c (1 ⊗ₜ[Γ(S, ⊤)] x) = p.appTop x :=
        AffineCoverCoefficientTensors.overlapTensorEquiv_one_tmul b f x
      have h := congrArg c (hrJ x hx)
      simpa only [map_mul, map_zero, hx'] using h
    have hRes : (W.ι ≫ p).appTop ≫ W.topIso.hom = p.appLE ⊤ W (by simp) := by
      rw [Scheme.Hom.comp_appTop]
      change p.app ⊤ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _ = _
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    apply W.topIso.commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    change ((W.ι ≫ p).appTop ≫ W.topIso.hom).hom x = 0
    rw [hRes]
    have : IsLocalization.Away (c r) Γ(Y, W) := (isAffineOpen_top Y).isLocalization_basicOpen _
    change algebraMap Γ(Y, ⊤) Γ(Y, W) (p.appTop x) = 0
    exact (IsLocalization.map_eq_zero_iff (.powers (c r)) Γ(Y, W) (p.appTop x)).mpr
      ⟨⟨c r, Submonoid.mem_powers _⟩, hrx⟩

end Langlands.AlgebraicGeometry
