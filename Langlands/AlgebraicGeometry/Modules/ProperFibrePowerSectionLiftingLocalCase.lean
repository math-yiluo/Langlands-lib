import Langlands.AlgebraicGeometry.Modules.ProperFibrePowerSectionLiftingLocalReduction
import Langlands.AlgebraicGeometry.Modules.ProperAdicCohomologyStableImageStatement
import Langlands.AlgebraicGeometry.Modules.IdealAdicLayers
import Langlands.AlgebraicGeometry.Modules.IdealAdicClosedFibre
import Langlands.AlgebraicGeometry.Modules.FinitePresentation
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Picard.LineBundleFinitePresentation
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof

/-! # The local closed-fibre case from stable images and layer vanishing -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections

/-- Uniform vanishing of first cohomology on the successive maximal-ideal layers of the
powers of a line bundle that is ample on the closed fibre of a proper scheme over a
noetherian local ring. -/
def LocalAdicLayerVanishing : Prop :=
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] [IsLocalRing A]
    (X Z : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f] (L : LineBundle X)
    (i : Z ⟶ X) (g : Z ⟶ Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))),
    IsPullback i g f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) →
    ((LineBundle.pullback i).obj L).IsAmple →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
        IsZero ((relativeCohomology f 1).obj
          (IdealAdic.adicLayer f (IsLocalRing.maximalIdeal A) (tensorPow L.obj n) k))

namespace LocalCase

/-- Surjectivity of the image of a morphism is unchanged by a natural isomorphism of
functors to modules. -/
lemma surjective_map_iff_of_iso {C : Type*} [Category C] {R : Type u} [Ring R]
    {F G : C ⥤ ModuleCat.{u} R} (e : F ≅ G) {M N : C} (φ : M ⟶ N) :
    Function.Surjective (F.map φ) ↔ Function.Surjective (G.map φ) := by
  have hG : G.map φ = e.inv.app M ≫ F.map φ ≫ e.hom.app N := by simp
  have hF : F.map φ = e.hom.app M ≫ G.map φ ≫ e.inv.app N := by simp
  constructor
  · intro hs
    rw [hG, ConcreteCategory.coe_comp, ConcreteCategory.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso (e.hom.app N)).2.comp hs).comp
      (ConcreteCategory.bijective_of_isIso (e.inv.app M)).2
  · intro hs
    rw [hF, ConcreteCategory.coe_comp, ConcreteCategory.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso (e.inv.app N)).2.comp hs).comp
      (ConcreteCategory.bijective_of_isIso (e.hom.app M)).2

/-- If the first cohomology of every successive ideal-adic layer of a quasi-coherent module
with finite affine sections vanishes, then, given the stable-image statement, every global
section of the pullback of the module to the base change of `Spec (R/I) → Spec R` lifts. -/
lemma surjective_sectionPullback_of_isZero_layer
    (hs : ProperAdicCohomologyStableImageStatement.{u})
    {R : CommRingCat.{u}} [IsNoetherianRing R] {I : Ideal R} {X Z : Scheme.{u}}
    {f : X ⟶ Spec R} [IsProper f] {i : Z ⟶ X} {g : Z ⟶ Spec (CommRingCat.of (R ⧸ I))}
    (hpb : IsPullback i g f (Spec.map (IdealAdic.quotientRingHom I)))
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (h₁ : ∀ k, IsZero ((relativeCohomology f 1).obj (IdealAdic.adicLayer f I M k))) :
    Function.Surjective (sectionPullback i M ⊤) := by
  obtain ⟨c, hc⟩ := hs R I X f inferInstance M inferInstance hM 0
  have hrange := hc 1 (1 + c) le_rfl
  have htr : Function.Surjective ((relativeGlobalSections f).map
      (IdealAdic.adicTransition f I M (Nat.le_trans (Nat.le_add_right 1 c) le_rfl))) :=
    IdealAdic.surjective_sections_adicTransition f I M h₁ _
  have htr0 := (surjective_map_iff_of_iso (relativeCohomologyZeroIso f) _).2 htr
  have hproj0 : Function.Surjective
      ((relativeCohomology f 0).map (IdealAdic.adicProjection f I M 1)) := by
    intro y
    have hy : y ∈ LinearMap.range
        ((relativeCohomology f 0).map (IdealAdic.adicProjection f I M 1)).hom := by
      rw [← hrange]
      obtain ⟨x, hx⟩ := htr0 y
      exact ⟨x, hx⟩
    exact hy
  have hproj := (surjective_map_iff_of_iso (relativeCohomologyZeroIso f) _).1 hproj0
  have hproj' : Function.Surjective ((IdealAdic.projection f I M).app ⊤) := by
    have hJ : ∀ J : Ideal R, J = I →
        Function.Surjective ((relativeGlobalSections f).map (IdealAdic.projection f J M)) →
          Function.Surjective ((IdealAdic.projection f I M).app ⊤) := by
      rintro J rfl h
      exact h
    exact hJ _ (pow_one I) hproj
  intro y
  obtain ⟨z, hz⟩ := hproj' ((IdealAdic.closedFibreIso hpb M).inv.app ⊤ y)
  refine ⟨z, ?_⟩
  have key : sectionPullback i M ⊤ z =
      (IdealAdic.closedFibreIso hpb M).hom.app ⊤ ((IdealAdic.projection f I M).app ⊤ z) := by
    change ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app ⊤ z = _
    rw [← IdealAdic.projection_closedFibreIso_hom hpb M]
    rfl
  rw [key, hz]
  exact LocalReduction.hom_app_inv_app (IdealAdic.closedFibreIso hpb M) ⊤ y

end LocalCase

open LocalCase in
/-- The closed-fibre section lifting over a noetherian local base follows from the stable
image statement for proper adic cohomology and uniform first-cohomology vanishing on the
maximal-ideal layers of large powers. -/
theorem localClosedFibrePowerSectionLifting_of_layerVanishing
    (hs : ProperAdicCohomologyStableImageStatement.{u})
    (hv : LocalAdicLayerVanishing.{u}) :
    LocalClosedFibrePowerSectionLifting.{u} := by
  intro A _ _ X Z f _ L i g hpb hamp
  obtain ⟨n₀, hn₀⟩ := hv A X Z f L i g hpb hamp
  refine ⟨n₀, fun n hn => ?_⟩
  have hL := tensorPow_isLocallyFreeRankOne X L n
  have : (tensorPow L.obj n).IsQuasicoherent := hL.isQuasicoherent
  have : (tensorPow L.obj n).IsFinitePresentation := hL.isFinitePresentation
  exact surjective_sectionPullback_of_isZero_layer hs hpb (tensorPow L.obj n)
    (hasFiniteAffineSections_of_isFinitePresentation _) (hn₀ n hn)

end Langlands.AlgebraicGeometry.Modules
