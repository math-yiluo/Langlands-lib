import Langlands.AlgebraicGeometry.Picard.DualNumberCocycles

/-! # Actual epsilon scaling on the arbitrary-scheme thickening -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Langlands.GroupScheme.GeneralLinear.DualNumber

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Actual base change of epsilon scaling on the dual-number test scheme. -/
def scale (c : k) : thickening f ⟶ thickening f :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (epsilonScale c).toRingHom)) (𝟙 _) (by simp) (by
      rw [Category.comp_id, dualNumberProjection, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact ((epsilonScale c).commutes a).symm)

@[reassoc (attr := simp)]
lemma scale_projection (c : k) : scale f c ≫ projection f = projection f := by
  simp only [scale, projection, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma scale_structure (c : k) :
    scale f c ≫ structureMap f =
      structureMap f ≫ Spec.map (CommRingCat.ofHom (epsilonScale c).toRingHom) := by
  simp only [scale, structureMap, pullback.map, pullback.lift_snd]

/-- The induced endomorphism of actual sections over an inverse-image open. -/
def scaleSectionMap (c : k) (U : X.Opens) :
    Γ(thickening f, projection f ⁻¹ᵁ U) ⟶ Γ(thickening f, projection f ⁻¹ᵁ U) :=
  (scale f c).appLE _ _ (by rw [← Scheme.Hom.comp_preimage, scale_projection])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma projection_scaleSectionMap (c : k) (U : X.Opens) :
    (projection f).app U ≫ scaleSectionMap f c U = (projection f).app U := by
  rw [scaleSectionMap]
  conv_lhs => rw [(projection f).app_eq_appLE]
  rw [Scheme.Hom.appLE_comp_appLE]
  have he : ∀ (g : thickening f ⟶ X), g = projection f →
      ∀ h : projection f ⁻¹ᵁ U ≤ g ⁻¹ᵁ U,
        g.appLE U (projection f ⁻¹ᵁ U) h = (projection f).app U := by
    rintro g rfl h
    exact ((projection f).app_eq_appLE).symm
  exact he _ (scale_projection f c) _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma testSectionMap_scaleSectionMap (c : k) (U : X.Opens) :
    testSectionMap f U ≫ scaleSectionMap f c U =
      CommRingCat.ofHom (epsilonScale c).toRingHom ≫ testSectionMap f U := by
  unfold testSectionMap scaleSectionMap
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE]
  simp only [scale_structure]
  rw [Scheme.Hom.comp_appLE]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (epsilonScale c).toRingHom)).appTop ≫
      (structureMap f).appLE ⊤ (projection f ⁻¹ᵁ U) _ = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
lemma baseSectionMap_comp_app {Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) :
    baseSectionMap f U ≫ g.app U = baseSectionMap (g ≫ f) (g ⁻¹ᵁ U) := by
  unfold baseSectionMap
  rw [Category.assoc, g.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma baseSectionMap_projection (U : X.Opens) :
    baseSectionMap f U ≫ (projection f).app U =
      CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫ testSectionMap f U := by
  rw [baseSectionMap_comp_app]
  have hc : projection f ≫ f = structureMap f ≫ dualNumberProjection k := pullback.condition
  have he := congrArg (fun g : thickening f ⟶ Spec (CommRingCat.of k) ↦
    baseSectionMap g (projection f ⁻¹ᵁ U)) hc
  rw [he]
  unfold baseSectionMap testSectionMap
  rw [Scheme.Hom.comp_appLE]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))).appTop ≫
      (structureMap f).appLE ⊤ (projection f ⁻¹ᵁ U) _ = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

lemma testSectionMap_constant (U : X.Opens) (c : k) :
    testSectionMap f U (algebraMap k (DualNumber k) c) =
      (projection f).app U (baseSectionMap f U c) :=
  (congrArg (fun r ↦ r.hom c) (baseSectionMap_projection f U)).symm

@[simp]
lemma scaleSectionMap_projection (c : k) (U : X.Opens) (a : Γ(X, U)) :
    scaleSectionMap f c U ((projection f).app U a) = (projection f).app U a :=
  congrArg (fun r ↦ r.hom a) (projection_scaleSectionMap f c U)

lemma scaleSectionMap_epsilon (c : k) (U : X.Opens) :
    scaleSectionMap f c U (epsilonSection f U) =
      (projection f).app U (baseSectionMap f U c) * epsilonSection f U := by
  have h := congrArg (fun r ↦ r.hom (DualNumber.eps : DualNumber k))
    (testSectionMap_scaleSectionMap f c U)
  change scaleSectionMap f c U (epsilonSection f U) =
    testSectionMap f U (epsilonScale c DualNumber.eps) at h
  rw [h]
  have he : epsilonScale c DualNumber.eps =
      algebraMap k (DualNumber k) c * DualNumber.eps := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [he, map_mul, testSectionMap_constant]
  rfl

/-- Actual scheme scaling becomes coefficient-ring epsilon scaling. -/
lemma scaleSectionMap_sectionMap (c : k) (U : X.Opens) :
    (scaleSectionMap f c U).hom.comp (sectionMap f U) =
      (sectionMap f U).comp (epsilonScale (baseSectionMap f U c)).toRingHom := by
  apply RingHom.ext
  intro z
  change scaleSectionMap f c U (sectionMap f U z) =
    sectionMap f U (epsilonScale (baseSectionMap f U c) z)
  simp only [sectionMap_apply, map_add, map_mul, scaleSectionMap_projection,
    scaleSectionMap_epsilon, epsilonScale_fst, epsilonScale_snd]
  ring

lemma scaleSectionMap_sectionEquiv (c : k) (U : X.Opens) (z : DualNumber Γ(X, U)) :
    scaleSectionMap f c U (sectionEquiv f U z) =
      sectionEquiv f U (epsilonScale (baseSectionMap f U c) z) :=
  DFunLike.congr_fun (scaleSectionMap_sectionMap f c U) z

/-- Pullback by the actual scaling map multiplies the infinitesimal coefficient. -/
lemma scaleSectionMap_coefficientUnit (c : k) (U : X.Opens) (a : Γ(X, U)) :
    Units.map (scaleSectionMap f c U).hom.toMonoidHom (coefficientUnit f U a) =
      coefficientUnit f U (baseSectionMap f U c * a) := by
  apply Units.ext
  change scaleSectionMap f c U (coefficientUnit f U a :
    Γ(thickening f, projection f ⁻¹ᵁ U)) = _
  rw [coefficientUnit_val, map_add, map_one, map_mul, scaleSectionMap_projection,
    scaleSectionMap_epsilon, coefficientUnit_val, map_mul]
  ring

/-- The actual scaling morphism fixes the zero section. -/
@[reassoc (attr := simp)]
lemma closedPoint_scale (c : k) : closedPoint f ≫ scale f c = closedPoint f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, scale_projection, closedPoint_projection]
  · rw [Category.assoc, scale_structure, closedPoint_structure_assoc]
    rw [closedPoint_structure]
    congr 1
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (epsilonScale c).toRingHom) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change (epsilonScale c z).fst = z.fst
    exact epsilonScale_fst c z

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
