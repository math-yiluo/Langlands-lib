import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # A local unit criterion for maps from a line bundle to the structure sheaf -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

/-- A morphism from a locally free rank-one module to the structure sheaf is an isomorphism
if every point has an open neighbourhood with a section sent to a unit. -/
theorem isIso_of_isUnit_app_locally {N : X.Modules} (hN : IsLocallyFreeRankOne N)
    (φ : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ x : X, ∃ (V : X.Opens) (n : Γ(N, V)), x ∈ V ∧
      IsUnit (M := Γ(X, V)) (φ.app V n)) :
    IsIso φ := by
  rw [isIso_iff_stalk_isIso]
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hN x
  obtain ⟨V, n, hxV, hn⟩ := h x
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom
  have hψ (y : U.toScheme) :
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ.mapPresheaf) ↔
        IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι y)).map
          ((Scheme.Modules.toPresheaf X).map φ)) := by
    change IsIso (((Scheme.Modules.toPresheaf U.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map ψ) ↔ _
    simp only [ψ, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
    exact isIso_stalk_restrict_iff φ U y
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  let i : U.ι ''ᵁ W ⟶ V := homOfLE (U.ι.image_preimage_le V)
  let n' : Γ(N.restrict U.ι, W) := N.presheaf.map i.op n
  let a : Γ(U.toScheme, W) := e.hom.app W n'
  have hφn : IsUnit (M := Γ(X, U.ι ''ᵁ W)) (φ.app (U.ι ''ᵁ W) (N.presheaf.map i.op n)) := by
    have hnat : φ.app (U.ι ''ᵁ W) (N.presheaf.map i.op n) =
        X.presheaf.map i.op (φ.app V n) :=
      ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) n
    rw [hnat]
    exact hn.map (X.presheaf.map i.op).hom
  have hψa : IsUnit (M := Γ(U.toScheme, W)) (ψ.app W a) := by
    have he : e.inv.app W a = n' := by
      change (e.hom ≫ e.inv).app W n' = n'
      rw [e.hom_inv_id]
      rfl
    have hψa' : ψ.app W a = (U.ι.appIso W).hom (φ.app (U.ι ''ᵁ W) n') := by
      change (Scheme.Modules.restrictUnitIso U.ι).hom.app W
        (φ.app (U.ι ''ᵁ W) (e.inv.app W a)) = _
      rw [he]
      rfl
    rw [hψa']
    exact hφn.map (U.ι.appIso W).hom.hom
  have hc : IsUnit (unitEndCoefficient ψ W) := by
    rw [unitEndCoefficient_app] at hψa
    exact isUnit_of_mul_isUnit_right hψa
  have hres := unitEnd_restrict_isIso ψ W hc
  have hxW : (⟨x, hxU⟩ : U.toScheme) ∈ W := hxV
  have hstalk : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hxU⟩ : U.toScheme)).map
      ψ.mapPresheaf) :=
    (isIso_stalk_restrict_iff ψ W ⟨⟨x, hxU⟩, hxW⟩).mp (by infer_instance)
  exact (hψ ⟨x, hxU⟩).mp hstalk

end Langlands.Scheme.Modules
