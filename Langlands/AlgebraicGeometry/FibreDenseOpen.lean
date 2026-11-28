import Langlands.Algebra.LocalFiberInjectivity
import Langlands.AlgebraicGeometry.FibreGenericPoints
import Langlands.AlgebraicGeometry.StalkEssFinitePresentation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk

/-! # Fibrewise dense opens of smooth schemes -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

namespace FibreGenerizationDense

variable {S X Y Z : Scheme.{u}}

/-- The intersection of two fibrewise dense opens is fibrewise dense. -/
theorem inf {p : X ⟶ S} {U V : X.Opens}
    (hU : FibreGenerizationDense p U) (hV : FibreGenerizationDense p V) :
    FibreGenerizationDense p (U ⊓ V : X.Opens) := by
  intro x
  obtain ⟨y, hy, hyx, hxy⟩ := hU x
  obtain ⟨z, hz, hzy, hyz⟩ := hV y
  exact ⟨z, ⟨hyz.mem_open U.isOpen hy, hz⟩, hzy.trans hyx, hyz.trans hxy⟩

/-- Flat morphisms lift same-fibre generizations in the target. -/
theorem preimage_flat {p : X ⟶ S} {U : X.Opens} (hU : FibreGenerizationDense p U)
    (q : Y ⟶ X) [Flat q] : FibreGenerizationDense (q ≫ p) (q ⁻¹ᵁ U : Y.Opens) := by
  intro x
  obtain ⟨y, hy, hpy, hyx⟩ := hU (q x)
  obtain ⟨z, hzx, hz⟩ := Flat.generalizingMap q hyx
  refine ⟨z, ?_, by simpa only [Scheme.Hom.comp_apply, hz] using hpy, hzx⟩
  change q z ∈ U
  rwa [hz]

/-- A fibrewise dense open remains fibrewise dense under arbitrary base change, since
on each residue fibre the change of scalars is a flat field extension. -/
theorem preimage_isPullback {p : X ⟶ S} {q : Y ⟶ S} {a : Z ⟶ X} {b : Z ⟶ Y}
    (sq : IsPullback a b p q) {U : X.Opens} (hU : FibreGenerizationDense p U) :
    FibreGenerizationDense b (a ⁻¹ᵁ U : Z.Opens) := by
  intro z
  let t := b z
  let sq' := isPullback_fiberToSpecResidueField_of_isPullback sq t
  let c : b.fiber t ⟶ p.fiber (q t) :=
    pullback.map _ _ _ _ a (Spec.map (q.residueFieldMap t)) q sq.w.symm (by simp)
  have hc : c ≫ p.fiberι (q t) = b.fiberι t ≫ a := pullback.lift_fst _ _ _
  have hflat : Flat (Spec.map (q.residueFieldMap t)) := by
    rw [Flat.SpecMap_iff, RingHom.Flat]
    let := (q.residueFieldMap t).hom.toAlgebra
    exact inferInstanceAs (Module.Flat (S.residueField (q t)) (Y.residueField t))
  have : Flat c := MorphismProperty.of_isPullback sq'.flip hflat
  have hz : p (a z) = q t := congrArg (fun g : Z ⟶ S => g z) sq.w
  obtain ⟨x, hx, hpx, hxz⟩ := hU (a z)
  let x' := (p.fiberHomeo (q t)).symm ⟨x, hpx.trans hz⟩
  have hx' : p.fiberι (q t) x' = x := p.fiberι_fiberHomeo_symm _ _
  have hcz : p.fiberι (q t) (c (b.asFiber z)) = a z := by
    rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]
  have hsp : x' ⤳ c (b.asFiber z) := by
    apply (p.fiberι (q t)).isEmbedding.specializes_iff.mp
    rwa [hx', hcz]
  obtain ⟨w, hw, hwc⟩ := Flat.generalizingMap c hsp
  refine ⟨b.fiberι t w, ?_, (b.fiberHomeo t w).2, ?_⟩
  · change a (b.fiberι t w) ∈ U
    rwa [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply, hwc, hx']
  · simpa only [t, Scheme.Hom.fiberι_asFiber] using hw.map (b.fiberι t).continuous

/-- An open immersion takes fibrewise dense opens to fibrewise dense opens in its image.
If the image is fibrewise dense in the target, the same holds there. -/
theorem image_open {p : X ⟶ S} (j : Y ⟶ X) [IsOpenImmersion j]
    (hj : FibreGenerizationDense p j.opensRange) {U : Y.Opens}
    (hU : FibreGenerizationDense (j ≫ p) U) : FibreGenerizationDense p (j ''ᵁ U : X.Opens) := by
  intro x
  obtain ⟨y, ⟨v, rfl⟩, hpy, hyx⟩ := hj x
  obtain ⟨w, hw, hpw, hwv⟩ := hU v
  exact ⟨j w, ⟨w, hw, rfl⟩, hpw.trans hpy, (hwv.map j.continuous).trans hyx⟩

end FibreGenerizationDense

section SchematicDensity

open IsLocalRing

private theorem regular_of_nonzero_in_fibre {R B : Type u} [CommRing R] [CommRing B]
    [IsLocalRing R] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Module.Flat R B] (hfp : Langlands.Algebra.EssFinitePresentation R B)
    (b : B) [IsDomain (B ⧸ (maximalIdeal R).map (algebraMap R B))]
    (hb : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R B)) b ≠ 0) :
    IsSMulRegular B b := by
  let μ : B →ₗ[B] B := LinearMap.mulLeft B b
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal R)
  have hb' : ((1 : ResidueField R) ⊗ₜ[R] b) ≠ 0 := by
    intro h
    apply hb
    apply e.injective
    rw [map_zero]
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B (maximalIdeal R) b).trans h
  have hdom : IsDomain (ResidueField R ⊗[R] B) := e.symm.toMulEquiv.isDomain
  have hμ : ∀ w, LinearMap.lTensor (ResidueField R) (μ.restrictScalars R) w =
      (1 ⊗ₜ[R] b) * w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a c => simp [μ, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b c]
    | add a c ha hc => simp [ha, hc, mul_add]
  have h := Langlands.Algebra.localFiberInjectivity R B B B μ hfp inferInstance inferInstance
    inferInstance (fun a c h => mul_left_cancel₀ hb' ((hμ a).symm.trans (h.trans (hμ c))))
  exact h.1

variable {S X : Scheme.{u}} (p : X ⟶ S) [Smooth p]

private lemma regular_germ_of_unit_at_fibre_generization {W : X.Opens} {x y : X}
    (hx : x ∈ W) (hyx : y ⤳ x) (hpy : p y = p x) (b : Γ(X, W))
    (hb : IsUnit (X.presheaf.germ W y (hyx.mem_open W.isOpen hx) b)) :
    IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ W x hx b) := by
  let R := S.presheaf.stalk (p x)
  let B := X.presheaf.stalk x
  let : Algebra R B := (p.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap R B) := inferInstanceAs (IsLocalHom (p.stalkMap x).hom)
  have : Module.Flat R B := Flat.stalkMap p x
  let F := p.fiber (p x)
  let j := p.fiberι (p x)
  let ξ := p.asFiber x
  let ζ := (p.fiberHomeo (p x)).symm ⟨y, hpy⟩
  have hξ : j ξ = x := p.fiberι_asFiber x
  have hζ : j ζ = y := p.fiberι_fiberHomeo_symm _ _
  have hspec : ζ ⤳ ξ := j.isEmbedding.specializes_iff.mp (by rwa [hζ, hξ])
  have hξW : ξ ∈ j ⁻¹ᵁ W := by change j ξ ∈ W; rwa [hξ]
  have hζW : ζ ∈ j ⁻¹ᵁ W := hspec.mem_open (j ⁻¹ᵁ W).isOpen hξW
  have hsm : Smooth (p.fiberToSpecResidueField (p x)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback p (S.fromSpecResidueField (p x))) inferInstance
  have : IsRegularLocalRing (F.presheaf.stalk ξ) :=
    @Smooth.isRegularLocalRing_stalkFLT (S.residueField (p x)) _ F
      (p.fiberToSpecResidueField (p x)) hsm ξ
  have : IsDomain (F.presheaf.stalk ξ) := IsRegularLocalRing.isDomainFLT _
  let e := quotientStalkEquivFiberStalk p x
  have : IsDomain (B ⧸ (maximalIdeal R).map (algebraMap R B)) := e.toMulEquiv.isDomain
  apply regular_of_nonzero_in_fibre (stalkEssFinitePresentation X S p x inferInstance)
  intro hzero
  change Ideal.Quotient.mk ((maximalIdeal R).map (p.stalkMap x).hom) _ = 0 at hzero
  have h0 := congrArg (quotientStalkEquivFiberStalk p x) hzero
  rw [map_zero, quotientStalkEquivFiberStalk_mk] at h0
  have hcast : (X.presheaf.stalkCongr (.of_eq hξ.symm)).hom (X.presheaf.germ W x hx b) =
      X.presheaf.germ W (j ξ) hξW b := by
    have he := X.presheaf.germ_stalkSpecializes hx (Inseparable.of_eq hξ).specializes
    exact congrArg (fun ψ : Γ(X, W) ⟶ X.presheaf.stalk (j ξ) => ψ b) he
  change (j.stalkMap ξ) ((X.presheaf.stalkCongr (.of_eq hξ.symm)).hom
    (X.presheaf.germ W x hx b)) = 0 at h0
  have h1 : F.presheaf.germ (j ⁻¹ᵁ W) ξ hξW (j.app W b) = 0 := by
    rw [hcast] at h0
    exact (j.germ_stalkMap_apply W ξ hξW b).symm.trans h0
  have h2 : F.presheaf.germ (j ⁻¹ᵁ W) ζ hζW (j.app W b) = 0 := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply _ hξW hspec, h1, map_zero]
  have hunit (z : X) (hz : z = y) (hzW : z ∈ W) : IsUnit (X.presheaf.germ W z hzW b) := by
    subst z
    exact hb
  exact ((hunit (j ζ) hζ hζW).map (j.stalkMap ζ).hom).ne_zero ((j.germ_stalkMap_apply W ζ hζW b).trans h2)

/-- A fibrewise dense open immersion into a smooth scheme is schematically dominant. -/
theorem FibreGenerizationDense.schematicallyDominant {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (h : FibreGenerizationDense p j.opensRange) :
    IsSchemeTheoreticallyDominant j := by
  refine ⟨Scheme.IdealSheafData.ext (funext fun W => ?_)⟩
  rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, eq_bot_iff]
  intro a ha
  rw [Ideal.mem_bot]
  have ha0 := j.ideal_ker_le W ha
  change j.app W.1 a = 0 at ha0
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  obtain ⟨_, ⟨y, rfl⟩, hpy, hsp⟩ := h x
  have hy : j y ∈ W.1 := hsp.mem_open W.1.isOpen hx
  have hy0 : X.presheaf.germ W.1 (j y) hy a = 0 := by
    have h0 := j.germ_stalkMap_apply W.1 y hy a
    rw [ha0, map_zero] at h0
    have hinj := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective
    apply hinj
    exact h0.trans ((j.stalkMap y).hom.map_zero).symm
  let yW : W.1 := ⟨j y, hy⟩
  let M := (W.2.primeIdealOf yW).asIdeal.primeCompl
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf yW
  let : IsLocalization M (X.presheaf.stalk (j y)) := W.2.isLocalization_stalk yW
  obtain ⟨b, hb⟩ := (IsLocalization.map_eq_zero_iff M (X.presheaf.stalk (j y)) a).mp hy0
  have hunit : IsUnit (X.presheaf.germ W.1 (j y) hy (b : Γ(X, W.1))) :=
    IsLocalization.map_units (X.presheaf.stalk (j y)) b
  have hreg := regular_germ_of_unit_at_fibre_generization p hx hsp hpy (b : Γ(X, W.1)) hunit
  change X.presheaf.germ W.1 x hx a = X.presheaf.germ W.1 x hx 0
  apply hreg
  change (X.presheaf.germ W.1 x hx).hom b * (X.presheaf.germ W.1 x hx).hom a =
    (X.presheaf.germ W.1 x hx).hom b * (X.presheaf.germ W.1 x hx).hom 0
  rw [← map_mul, hb, map_zero, mul_zero]

end SchematicDensity

end Langlands.AlgebraicGeometry
