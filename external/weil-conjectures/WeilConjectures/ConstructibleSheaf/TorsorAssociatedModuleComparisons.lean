/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorInvariantSections
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Pullback and coefficient comparisons for associated module sheaves

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-associated-module-comparisons)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation along a local torsor section trivializes the associated module sheaf
upstairs. The trivial coefficient representation descends to the coefficient sheaf.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-associated-module-comparisons)

Proof:
1. Over the pullback of the torsor to its total space, use the diagonal section. An
   equivariant locally constant section is determined by evaluation at this section;
   conversely extend a locally constant section by the representation action on each
   translate of the diagonal. The torsor isomorphism identifies these translates with
   all of the pulled-back torsor. These inverse formulas are linear and commute with
   etale restrictions and intertwining maps. The equivariant section presheaf is a
   sheaf: glue on the induced etale cover of the total space, and use uniqueness of
   gluing to preserve equivariance. Thus sheafification does not change its sections.
   The evaluation formulas give the natural pullback comparison, including the scalar
   restriction in the definition of the associated functor.
2. For the trivial representation the equivariance condition is invariance. On an
   etale cover admitting a torsor section, an invariant locally constant function on
   the torsor is a unique locally constant function downstairs. Changing the section
   translates it by a group element, so invariance identifies the resulting functions
   on overlaps. Glue them downstairs. Pullback and this descent are inverse linear
   maps, natural in the etale object, giving the coefficient comparison. Neither
   argument imposes finite generation on the module. -/
theorem Scheme.GaloisCover.associatedModuleFunctor_comparisons
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P] :
    let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
    let T := c.associatedModuleFunctor ℓ
    Nonempty (T ⋙ (c.π)^*[C] ≅
      forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ⋙
        constantSheaf c.P.smallEtaleTopology C) ∧
    Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
      (constantSheaf V.smallEtaleTopology C).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  dsimp only
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let S := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  let F := c.equivariantModulePresheafFunctor ℓ ⋙
    (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj S
  let T := c.associatedModuleFunctor ℓ
  obtain ⟨d⟩ := c.equivariantModulePresheaf_diagonal ℓ
  obtain ⟨t⟩ := c.equivariantModulePresheaf_trivial ℓ
  constructor
  · let R := Etale.localizationRestriction C c.π c.etale
    let K := forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
      S ⋙ constantSheaf c.P.smallEtaleTopology C
    have h : T ⋙ R ≅ K :=
      (Functor.isoWhiskerLeft F
        ((MorphismProperty.Over.map ⊤ c.etale).pushforwardContinuousSheafificationCompatibility
          C (c.P.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).symm) ≪≫
      Functor.isoWhiskerRight d (presheafToSheaf c.P.smallEtaleTopology C) ≪≫
      Functor.isoWhiskerLeft K (sheafificationNatIso c.P.smallEtaleTopology C).symm
    exact ⟨Functor.isoWhiskerLeft T
      (Etale.upperStarIsoLocalizationRestriction C c.π c.etale) ≪≫
      h⟩
  · exact ⟨(presheafToSheaf V.smallEtaleTopology C).mapIso t ≪≫
      (sheafificationIso ((constantSheaf V.smallEtaleTopology C).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))).symm⟩

end AlgebraicGeometry
