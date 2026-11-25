/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open Scheme

/-- Base extension from a separably closed field is injective on module sections.
Source: Stacks Tag 0A3I and the canonical coefficient-forgetting comparison.

Proof: Equip K with the k-algebra structure of Spec.preimage t. Apply
etale_sections_base_field_extension to S with structure morphism p and to the
underlying set sheaf of F. Its unit evaluated at the identity etale object is
bijective. The canonical terminal-object isomorphism turns this into the map on
global sections. isIso_upperStar_forget_comparison identifies the set inverse
image with the underlying set sheaf of the module inverse image; the homEquiv
formula for this comparison identifies their units. Thus the module restriction
has bijective underlying function. The isomorphism from the given pullback square
to the canonical pullback transports this statement to i. Empty S and the zero
coefficient ring cause no exception, since all these comparisons are functorial.
(blueprint: new-etale-module-sections-field-extension) -/
theorem etaleModuleSectionsFieldExtension_injective
    (Λ : Type (u + 1)) [CommRing Λ]
    (k K : Type u) [Field k] [Field K] [IsSepClosed k]
    {S S' : Scheme.{u}} (p : S ⟶ Spec (.of k))
    (t : Spec (.of K) ⟶ Spec (.of k))
    (i : S' ⟶ S) (p' : S' ⟶ Spec (.of K)) (sq : IsPullback i p' p t)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Injective (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F).hom := by
  let : Algebra k K := (Spec.preimage t).hom.toAlgebra
  have hcanonical (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
      (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) G) := by
    let R := Λ
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let F := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj G
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).smallGrothendieckTopology
        @Etale)
    let H := (sheafCompose _ (forget (ModuleCat.{u + 1} R))).obj
      ((p)^*[ModuleCat.{u + 1} R].obj G)
    let c := (adj.homEquiv F H).symm
      ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G))
    have : IsIso c := isIso_upperStar_forget_comparison R p G
    let : X.Over (Spec (.of k)) := ⟨f⟩
    have hb := etale_sections_base_field_extension k K X F
    have hc : Function.Bijective (c.hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj (Scheme.Etale.mk (𝟙 X))))) :=
      (isIso_iff_bijective _).mp (inferInstance)
    have hfac := congrArg (fun a ↦ a.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X))))
      ((adj.homEquiv F H).apply_symm_apply
        ((sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G)))
    rw [Adjunction.homEquiv_unit] at hfac
    change (adj.unit.app F).hom.app (Opposite.op (Scheme.Etale.mk (𝟙 X))) ≫
      c.hom.app (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj
        (Scheme.Etale.mk (𝟙 X)))) =
      (forget (ModuleCat.{u + 1} R)).map
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
          (Opposite.op (Scheme.Etale.mk (𝟙 X)))) at hfac
    have hu : Function.Bijective
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
          (Opposite.op (Scheme.Etale.mk (𝟙 X)))) := by
      change Function.Bijective ((forget (ModuleCat.{u + 1} R)).map
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
          (Opposite.op (Scheme.Etale.mk (𝟙 X)))))
      rw [← hfac]
      exact hc.comp hb
    have : IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
        (Opposite.op (Scheme.Etale.mk (𝟙 X)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hu
    unfold globalSectionsUpperStarMap
    have ht : IsIso (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        (Opposite.op (⊤_ X.Etale))).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G)) := by
      change IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom.app
        (Opposite.op (⊤_ X.Etale)))
      let e := terminalIsoIsTerminal (MorphismProperty.Over.mkIdTerminal @Etale X)
      let T := ((p)_*[ModuleCat.{u + 1} R].obj ((p)^*[ModuleCat.{u + 1} R].obj G)).obj
      let α : G.obj ⟶ T := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).unit.app G).hom
      have he : IsIso (α.app (Opposite.op (⊤_ X.Etale)) ≫ T.map e.inv.op) := by
        rw [← α.naturality]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (T.map e.inv.op)
    infer_instance
  have ht : Spec.map (CommRingCat.ofHom (algebraMap k K)) = t := Spec.map_preimage t
  let v := pullback.fst p t
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) v F) := by
    have hc := hcanonical S p F
    rw [ht] at hc
    exact hc
  let e := sq.isoPullback
  have hi : e.hom ≫ v = i := sq.isoPullback_hom_fst
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) e.hom v i hi.symm).hom.app F)) := by
    rw [globalSectionsUpperStarMap_comp']
    infer_instance
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) :=
    IsIso.of_isIso_comp_right _ ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) e.hom v i hi.symm).hom.app F))
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end AlgebraicGeometry.Etale
