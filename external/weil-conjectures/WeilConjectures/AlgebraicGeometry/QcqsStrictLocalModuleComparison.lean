/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalRestrictionNaturality
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalRestrictionIsomorphism

/-! # The module-valued strict-local continuity comparison

Source: Stacks Project, Tag 03Q9, degree zero and the canonical restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The terminal section of the iterated pullback corresponding to a strict-local limit leg.
The symmetry puts the base change in the orientation `X ×_Y Spec R`.
Source: Stacks Project, Tag 03Q9, proof.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison). -/
noncomputable def qcqsStrictLocalNeighbourhoodSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (pullback f (Scheme.strictLocalizationToBase s))) ⟶
      (pullback.fst f (Scheme.strictLocalizationToBase s)).Etale.obj
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)

/-- Restrict a section on the neighbourhood base change to strict-local global sections.
This is the actual module adjunction unit, followed by the specified limit leg and the
terminal-section/global-section isomorphism.
Source: Stacks Project, Tag 03Q9, proof.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison). -/
noncomputable def qcqsStrictLocalSectionRestriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
    (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj
      ((upperStar (ModuleCat.{u + 1} Λ)
        (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictLocalizationToBase s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F).obj.map
        (qcqsStrictLocalNeighbourhoodSection f s j).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictLocalizationToBase s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _

/-- The germ formula characterizing a module strict-local comparison.
Source: Stacks Project, Tag 03Q9, canonical representative restriction.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison). -/
def IsQcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F)) : Prop :=
  ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
    (Scheme.pointSmallEtale s).toPresheafFiber
      ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ a =
        qcqsStrictLocalSectionRestriction Λ f s F j

/-- Qcqs continuity for module coefficients, with its canonical representative formula.
Source: Stacks Project, Tag 03Q9, degree zero; Tags 03D3 and 03D7 for inverse images.
(blueprint: lem-weil-pbc-qcqs-strict-local-module-comparison).

Proof: apply `sets_pushforward_stalk_strictHenselization` to the underlying set sheaf.
The stalk is the filtered colimit over pointed neighbourhoods. The module forgetful functor
preserves these colimits (shrink the universe of its filtered-colimit instance), so it
identifies the underlying set of the module stalk with that set stalk. The canonical
inverse-image comparison `isIso_upperStar_forget_comparison` identifies the set pullback
with the underlying set of the module pullback; its adjoint-transpose definition identifies
their units. Evaluation at the terminal object and the global-section isomorphism then
transport the set comparison to the displayed target, after pullback symmetry. Each
representative restriction is linear, and the filtered module colimit gives a linear map
with precisely the displayed germ formula. The set comparison is bijective, so this
linear map is an isomorphism. All transports preserve the units and restriction maps,
which gives `IsQcqsStrictLocalModuleComparison`. No properness is used. The empty source
and zero coefficient ring yield zero modules and the same comparison. -/
theorem exists_qcqsStrictLocalModuleComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ e : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≅
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F),
      IsQcqsStrictLocalModuleComparison Λ f s F e.hom := by
  classical
  let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let : N.Initial := (Scheme.strictHenselizationAffineProperties s).1
  let P := ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj
  let stalkCocone := ((Scheme.pointSmallEtale s).presheafFiberCocone P).whisker N.op
  have hc : IsColimit stalkCocone :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P)
  let r := qcqsStrictLocalSectionRestriction Λ f s F
  let c : Cocone (N.op ⋙ (Functor.Elements.π (Scheme.pointSmallEtale s).fiber).op ⋙ P) :=
    { pt := _
      ι := { app := fun j ↦ r j.unop
             naturality := fun j k a ↦ by
               change F.obj.map
                 ((Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale).map a.unop).op ≫
                   r k.unop = r j.unop ≫ 𝟙 _
               rw [Category.comp_id]
               exact qcqsStrictLocalRestriction_naturality Λ f s F r (fun _ ↦ rfl) a.unop } }
  let a := hc.desc c
  have ha : IsQcqsStrictLocalModuleComparison Λ f s F a := by
    intro j
    exact hc.fac c (op j)
  have : IsIso a := isIso_qcqsStrictLocalRestriction_of_formula Λ f s F a ha
  exact ⟨asIso a, ha⟩

end AlgebraicGeometry.Etale
