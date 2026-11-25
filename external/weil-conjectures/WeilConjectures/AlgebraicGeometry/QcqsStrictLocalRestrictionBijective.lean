/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

import WeilConjectures.AlgebraicGeometry.StrictLocalModuleSectionsSetTransport

/-! # Bijectivity of strict-local restriction maps
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-module-restriction-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The underlying function of a linear map satisfying the representative formula is bijective.
This asserts only invertibility of an already constructed map, not its existence.
Source: Stacks Project, Tag 03Q9, degree zero; Tags 03D3 and 03D7 for inverse images.
(blueprint: lem-weil-pbc-strict-local-module-restriction-bijective).

Proof: Forget modules. The forgetful functor preserves filtered colimits, hence identifies
this map's source with the set stalk, with the same germ maps. The canonical module/set
inverse-image comparison is invertible and its adjoint-transpose identity identifies its
unit with the forgotten module unit. Transport the target across that comparison,
pullback symmetry and the terminal-section/global-section identification. The assumed
representative equations now say that the transported map is the unique map in
sets_pushforward_stalk_strictHenselization. That theorem makes it bijective. All target
transports are bijections, so the original linear map is bijective, hence invertible.
The argument uses qcqs continuity but no properness or torsion, and includes the empty
source and zero coefficient ring. -/
theorem bijective_qcqsStrictLocalRestriction_of_formula
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F))
    (ha : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictLocalizationToBase s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictLocalizationToBase s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    Function.Bijective (ConcreteCategory.hom a) := by
  classical
  let U := forget (ModuleCat.{u + 1} Λ)
  let H := (sheafCompose X.smallEtaleTopology U).obj F
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} U
  let γ := (Scheme.pointSmallEtale s).sheafFiberCompIso U
  let e := strictLocalModuleSectionsSetEquiv Λ f s F
  have he := strictLocalModuleSections_set_transport Λ f s F
  obtain ⟨_, Θ, _, hbij, huniq⟩ := sets_pushforward_stalk_strictHenselization f H s
  let b := fun t ↦ e (ConcreteCategory.hom a ((γ.hom.app P) t))
  have hb : b = Θ := by
    apply huniq
    intro j z
    dsimp only [b]
    have hγ := ConcreteCategory.congr_hom
      ((Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app U
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        P.obj) z
    change (γ.hom.app P) _ = _ at hγ
    erw [hγ]
    have h := ConcreteCategory.congr_hom (ha j) z
    change ConcreteCategory.hom a _ = _ at h
    erw [h]
    exact he j z
  have hb' : Function.Bijective b := hb ▸ hbij
  have hγbij := ConcreteCategory.bijective_of_isIso (γ.hom.app P)
  constructor
  · intro x y hxy
    obtain ⟨x', rfl⟩ := hγbij.2 x
    obtain ⟨y', rfl⟩ := hγbij.2 y
    exact congrArg (fun t ↦ (γ.hom.app P) t) (hb'.1 (congrArg e hxy))
  · intro y
    obtain ⟨x, hx⟩ := hb'.2 (e y)
    exact ⟨(γ.hom.app P) x, e.injective hx⟩

end AlgebraicGeometry.Etale
