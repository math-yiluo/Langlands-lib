import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.Modules.TensorSections

/-!
# Global sections of trivial modules and of restriction units

Over an affine base `Spec T`, the `T`-module of global sections of the structure module is
`T` itself when the structure map is an isomorphism on global functions. The global sections of
the adjunction unit `𝒪 ⟶ j_* j^* 𝒪` are then bijective whenever both structure maps are
isomorphisms on global functions, and a morphism out of the structure module whose image under
the unit is a frame of a trivial pullback has invertible pullback.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

set_option backward.isDefEq.respectTransparency false

/-- The `T`-module global sections of the structure module along `h : Y ⟶ Spec T` are `T`
when `h` is an isomorphism on global functions. -/
theorem nonempty_relativeGlobalSections_unit_equiv {T : CommRingCat.{u}} {Y : Scheme.{u}}
    (h : Y ⟶ Spec T) [IsIso h.appTop] :
    Nonempty ((DerivedSections.relativeGlobalSections h).obj
      (SheafOfModules.unit Y.ringCatSheaf) ≃ₗ[T] T) := by
  let ρ : T ⟶ Γ(Y, ⊤) := DerivedSections.structureRingHom h
  have hρ : Function.Bijective ρ.hom := by
    have : IsIso ρ := by
      change IsIso ((Scheme.ΓSpecIso T).inv ≫ h.appTop)
      infer_instance
    exact (asIso ρ).commRingCatIsoToRingEquiv.bijective
  let M := (DerivedSections.relativeGlobalSections h).obj (SheafOfModules.unit Y.ringCatSheaf)
  let φ : T →ₗ[T] M := LinearMap.toSpanSingleton T M (1 : Γ(Y, ⊤))
  have hφ : ∀ t : T, (φ t : Γ(Y, ⊤)) = ρ.hom t := by
    intro t
    change ρ.hom t * (1 : Γ(Y, ⊤)) = ρ.hom t
    rw [mul_one]
  have hb : Function.Bijective φ := by
    have : (fun t ↦ (φ t : Γ(Y, ⊤))) = ρ.hom := funext hφ
    exact (by rw [this]; exact hρ : Function.Bijective (fun t ↦ (φ t : Γ(Y, ⊤))))
  exact ⟨(LinearEquiv.ofBijective φ hb).symm⟩

/-- Global sections along `g' ≫ f'` of a trivial module pushed forward along `g'` are `T`. -/
theorem nonempty_relativeGlobalSections_pushforward_equiv {T : CommRingCat.{u}}
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Spec T) (g' : Y' ⟶ X') [IsIso (g' ≫ f').appTop]
    (W : Y'.Modules) (hW : Nonempty (W ≅ SheafOfModules.unit Y'.ringCatSheaf)) :
    Nonempty ((DerivedSections.relativeGlobalSections f').obj
      ((Scheme.Modules.pushforward g').obj W) ≃ₗ[T] T) := by
  obtain ⟨e⟩ := nonempty_relativeGlobalSections_unit_equiv (g' ≫ f')
  let i := (DerivedSections.relativeGlobalSectionsCompIso g' f').app W ≪≫
    (DerivedSections.relativeGlobalSections (g' ≫ f')).mapIso hW.some
  exact ⟨i.toLinearEquiv.trans e⟩

/-- The structure comparison `𝒪 ⟶ j_* 𝒪` is the adjunction unit at `𝒪` followed by the direct
image of the canonical identification `j^* 𝒪 ≅ 𝒪`. -/
theorem unitToPushforwardUnit_eq {X Y : Scheme.{u}} (j : Y ⟶ X) :
    Langlands.Scheme.Modules.unitToPushforwardUnit j =
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pushforward j).map (Langlands.Scheme.Modules.pullbackUnitIso j).hom := by
  rw [← Langlands.Scheme.Modules.pullbackUnitAdjunction Y X j]
  exact Adjunction.homEquiv_unit _ _ _ _

/-- Global sections of the unit `𝒪 ⟶ j_* j^* 𝒪` are bijective when both `X' ⟶ Spec T` and
`Y' ⟶ Spec T` are isomorphisms on global functions. -/
theorem isIso_relativeGlobalSections_map_unit_unit {T : CommRingCat.{u}} {X' Y' : Scheme.{u}}
    (f' : X' ⟶ Spec T) (j : Y' ⟶ X') [IsIso f'.appTop] [IsIso (j ≫ f').appTop] :
    IsIso ((DerivedSections.relativeGlobalSections f').map
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        (SheafOfModules.unit X'.ringCatSheaf))) := by
  have hj : IsIso j.appTop := by
    have e : j.appTop = inv f'.appTop ≫ (j ≫ f').appTop := by
      rw [Scheme.Hom.comp_appTop, IsIso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  have h₁ : IsIso ((DerivedSections.relativeGlobalSections f').map
      (Langlands.Scheme.Modules.unitToPushforwardUnit j)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (asIso j.appTop).commRingCatIsoToRingEquiv.bijective
  rw [unitToPushforwardUnit_eq, Functor.map_comp] at h₁
  exact IsIso.of_isIso_comp_right _
    ((DerivedSections.relativeGlobalSections f').map
      ((Scheme.Modules.pushforward j).map (Langlands.Scheme.Modules.pullbackUnitIso j).hom))

/-- Invertibility of a functor applied to an adjunction unit is invariant under replacing the
object by an isomorphic one. -/
theorem isIso_map_unit_app_of_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : C ⥤ E) {M O : C} (θ : M ≅ O)
    (h : IsIso (F.map (adj.unit.app O))) : IsIso (F.map (adj.unit.app M)) := by
  have e : adj.unit.app M = θ.hom ≫ adj.unit.app O ≫ R.map (L.map θ.inv) := by
    have := adj.unit.naturality θ.inv
    simp only [Functor.id_map, Functor.comp_map] at this
    rw [← this, Iso.hom_inv_id_assoc]
  rw [e, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- If the unit sends a global section `σ` to the section `ζ⁻¹(1)` of a trivialized pullback,
then the pullback of the morphism defined by `σ` is an isomorphism. -/
theorem isIso_pullback_map_of_unit_app {X Y : Scheme.{u}} (g : Y ⟶ X) {M : X.Modules}
    (ζ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (σ : structureModule X ⟶ M)
    (hσ : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤
        (σ.app ⊤ (1 : Γ(X, ⊤))) = ζ.inv.app (g ⁻¹ᵁ ⊤) (1 : Γ(Y, g ⁻¹ᵁ ⊤))) :
    IsIso ((Scheme.Modules.pullback g).map σ) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  have key : (Scheme.Modules.pullback g).map σ ≫ ζ.hom =
      (Langlands.Scheme.Modules.pullbackUnitIso g).hom := by
    apply (adj.homEquiv _ _).injective
    refine Eq.trans ?_ (Langlands.Scheme.Modules.pullbackUnitAdjunction Y X g).symm
    rw [adj.homEquiv_naturality_left, adj.homEquiv_unit]
    apply (sectionHomEquiv _).symm.injective
    change ((σ ≫ adj.unit.app M ≫ (Scheme.Modules.pushforward g).map ζ.hom).app ⊤)
        (1 : Γ(X, ⊤)) =
      (Scheme.Modules.Hom.app (Langlands.Scheme.Modules.unitToPushforwardUnit g) ⊤)
        (1 : Γ(X, ⊤))
    change ζ.hom.app (g ⁻¹ᵁ ⊤) ((adj.unit.app M).app ⊤ (σ.app ⊤ (1 : Γ(X, ⊤)))) =
      g.app ⊤ (1 : Γ(X, ⊤))
    rw [hσ]
    have h1 : (g.app ⊤).hom (1 : Γ(X, ⊤)) = (1 : Γ(Y, g ⁻¹ᵁ ⊤)) := map_one _
    refine Eq.trans ?_ h1.symm
    change (ζ.inv ≫ ζ.hom).app (g ⁻¹ᵁ ⊤) (1 : Γ(Y, g ⁻¹ᵁ ⊤)) = (1 : Γ(Y, g ⁻¹ᵁ ⊤))
    rw [Iso.inv_hom_id]
    rfl
  have e : (Scheme.Modules.pullback g).map σ =
      (Langlands.Scheme.Modules.pullbackUnitIso g).hom ≫ ζ.inv := by
    rw [← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
