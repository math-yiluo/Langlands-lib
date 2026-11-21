import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Sections of finite products of module sheaves over opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.OpenSectionProducts

variable {X : Scheme.{u}} {ι : Type} [Finite ι]

/-- Sections over an open of a finite product of module sheaves are the product of the
sections. -/
def piSectionsIso (N : ι → X.Modules) (V : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V)).obj (∏ᶜ N) ≅
      ModuleCat.of _
        (∀ j, (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V)).obj (N j)) :=
  PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V)) N ≪≫
    ModuleCat.piIsoPi _

lemma piSectionsIso_hom_apply (N : ι → X.Modules) (V : X.Opens) (t : Γ(∏ᶜ N, V)) (j : ι) :
    (piSectionsIso N V).hom t j = (Pi.π N j).app V t := by
  have h1 : (piSectionsIso N V).hom t j =
      Pi.π (fun j => (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V)).obj (N j)) j
        ((PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V))
          N).hom t) := by
    rw [← ModuleCat.piIsoPi_hom_ker_subtype]
    rfl
  rw [h1]
  erw [PreservesProduct.iso_hom, ← ConcreteCategory.comp_apply, piComparison_comp_π]
  rfl

/-- If a morphism of module sheaves becomes an isomorphism after pullback to an open `W`,
then it is bijective on sections over every open contained in `W`. -/
lemma bijective_app_of_isIso_pullback {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens)
    (h : IsIso ((Scheme.Modules.pullback W.ι).map φ)) {V : X.Opens} (hV : V ≤ W) :
    Function.Bijective (φ.app V) := by
  have hR : IsIso ((Scheme.Modules.restrictFunctor W.ι).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι) φ).mpr h
  have key : ∀ V' : (W : Scheme.{u}).Opens, Function.Bijective (φ.app (W.ι ''ᵁ V')) := by
    intro V'
    have : IsIso ((Scheme.Modules.toPresheaf _).map
        ((Scheme.Modules.restrictFunctor W.ι).map φ)) := inferInstance
    have : IsIso (((Scheme.Modules.toPresheaf _).map
        ((Scheme.Modules.restrictFunctor W.ι).map φ)).app (Opposite.op V')) := inferInstance
    exact ConcreteCategory.bijective_of_isIso (((Scheme.Modules.toPresheaf _).map
        ((Scheme.Modules.restrictFunctor W.ι).map φ)).app (Opposite.op V'))
  have hV' : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hV
  have := key (W.ι ⁻¹ᵁ V)
  rwa [hV'] at this

/-- If the product of a finite family of morphisms becomes an isomorphism after pullback to
an open `W`, then joint evaluation of sections is bijective over every open inside `W`. -/
lemma bijective_pi_app_of_isIso_pullback {M : X.Modules} {N : ι → X.Modules}
    (f : ∀ j, M ⟶ N j) (W : X.Opens) (h : IsIso ((Scheme.Modules.pullback W.ι).map (Pi.lift f)))
    {V : X.Opens} (hV : V ≤ W) :
    Function.Bijective (fun (s : Γ(M, V)) (j : ι) => (f j).app V s) := by
  have hb := bijective_app_of_isIso_pullback (Pi.lift f) W h hV
  have hc : (fun (s : Γ(M, V)) (j : ι) => (f j).app V s) =
      (piSectionsIso N V).hom ∘ (Pi.lift f).app V := by
    funext s j
    change _ = (piSectionsIso N V).hom ((Pi.lift f).app V s) j
    rw [piSectionsIso_hom_apply, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, Pi.lift_comp_π]
  rw [hc]
  exact (ConcreteCategory.bijective_of_isIso (piSectionsIso N V).hom).comp hb

end Langlands.AlgebraicGeometry.Modules.OpenSectionProducts
