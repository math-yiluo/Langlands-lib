/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison

/-! # Module sections after algebraically closed field extension

Source: Stacks Project, Tag 0A3I, applied to the underlying sheaf of sets.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Scalar extension preserves global sections of every module-valued etale sheaf.
Source: Stacks Project, Tag 0A3I; the coefficient-forgetting comparison is the
Kan-extension/sheafification comparison of inverse images.
(blueprint: lem-sc-algclosed-extension-module-sections)

Proof: forget the module structure of G to obtain a sheaf of sets. By Tag 0A3I,
restriction on its global sections along X_K -> X is bijective, since k is separably
closed. The module forgetful functor preserves limits and filtered colimits, hence
commutes with inverse image: compute the Kan extension by filtered etale neighborhoods,
then sheafify. The comparison respects the adjunction unit. Evaluation at the terminal
etale object and the global-sections/terminal-sections isomorphisms therefore identify
the underlying function of the displayed module map with that restriction, conjugated
by the comparison bijections. A bijective module homomorphism is an isomorphism. No
quasi-compactness, torsion, primality, or invertibility assumption is needed. This
includes n = 0, n = 1, and the empty scheme. -/
theorem isIso_globalSectionsUpperStarMap_algClosed_extension
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) :
    IsIso (globalSectionsUpperStarMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) G) := by
  let R := ULift.{u + 1} (ZMod n)
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

end AlgebraicGeometry.Etale
