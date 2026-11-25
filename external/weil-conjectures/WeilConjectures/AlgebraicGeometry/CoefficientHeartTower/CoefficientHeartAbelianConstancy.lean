/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.Sites.TypePointFunctions
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom

/-! # Abelian constancy and the constant-sheaf counit

Source: coefficient-heart proof (1), pointed finite trivializations.
(blueprint: lem-sfb-coefficient-heart-abelian-constancy)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

/-- Constant abelian sheaves on a connected scheme are fully faithful.
Source: coefficient-heart proof (1), uniqueness of pointed trivializations.
(blueprint: lem-sfb-coefficient-heart-abelian-constancy)
Proof: the constant-sheaf unit on global sections is bijective, since a locally constant
section on a connected scheme is constant. The adjunction unit criterion gives full
faithfulness. -/
def fullyFaithfulAbConstant (X : Scheme.{u}) [ConnectedSpace X] :
    (constantSheaf X.smallEtaleTopology Ab.{u + 1}).FullyFaithful := by
  let adj := constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale X)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun P ↦ ?_
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.bijective_toSheafify_app_terminal X P)
  exact adj.fullyFaithfulLOfIsIsoUnit

/-- The same full faithfulness holds on the site localized at a connected etale object.
Source: coefficient-heart proof (1), uniqueness on connected finite covers.
(blueprint: lem-sfb-coefficient-heart-abelian-constancy)
Proof: the localized site is equivalent to the etale site of the object. This equivalence
commutes with the constant-sheaf functors. Transfer full faithfulness through this natural
isomorphism and cancel the fully faithful equivalence of sheaf categories. -/
def fullyFaithfulAbConstantOver {X : Scheme.{u}} (U : X.Etale)
    [ConnectedSpace U.left] :
    (constantSheaf (X.smallEtaleTopology.over U) Ab.{u + 1}).FullyFaithful := by
  let e := Scheme.Etale.overEquiv U
  let J := X.smallEtaleTopology.over U
  let K := U.left.smallEtaleTopology
  let η := e.constantSheafSheafCongrIso J K Ab.{u + 1} Over.mkIdTerminal
  exact Functor.FullyFaithful.ofCompFaithful
    ((fullyFaithfulAbConstant U.left).ofIso η.symm)

/-- Constancy of the underlying set inverse image implies constancy of the abelian one.
Source: coefficient-heart proof (1), recovering finite linear trivializations.
(blueprint: lem-sfb-coefficient-heart-abelian-constancy)
Proof: inverse image commutes with the forgetful functor. The underlying-set constant
functor is fully faithful on a connected scheme, so the constant/global-sections counit
is an isomorphism for a constant set sheaf. Its abelian counit has that same underlying
map, up to the canonical constant/forget comparison. The forgetful functor reflects
isomorphisms. Thus the abelian counit is an isomorphism and supplies constancy. -/
theorem abelianPullback_isConstant_of_set {X Y : Scheme.{u}} [ConnectedSpace Y]
    (f : Y ⟶ X) (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : ((Scheme.etaleSetPullback f).obj
      ((sheafCompose X.smallEtaleTopology (forget Ab.{u + 1})).obj F)).IsConstant
        Y.smallEtaleTopology) :
    ((Etale.upperStar Ab.{u + 1} f).obj F).IsConstant Y.smallEtaleTopology := by
  let G := (Etale.upperStar Ab.{u + 1} f).obj F
  have hL : PreservesFiniteLimits (Scheme.etaleSetPullback f) := by
    unfold Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, _⟩ := etaleInverseImageAbelianLift_hom Y X f hL
  have hsource : ((sheafCompose X.smallEtaleTopology (forget Ab.{u + 1}) ⋙
      Scheme.etaleSetPullback f).obj F).IsConstant Y.smallEtaleTopology := hF
  have hG : ((sheafCompose Y.smallEtaleTopology (forget Ab.{u + 1})).obj G).IsConstant
      Y.smallEtaleTopology :=
    Sheaf.isConstant_congr Y.smallEtaleTopology (ea.app F).symm
  let adj := constantSheafAdj Y.smallEtaleTopology Ab.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale Y)
  have hforget : IsIso
      ((sheafCompose Y.smallEtaleTopology (forget Ab.{u + 1})).map (adj.counit.app G)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  have : IsIso (adj.counit.app G) :=
    isIso_of_reflects_iso _ (sheafCompose Y.smallEtaleTopology (forget Ab.{u + 1}))
  exact Sheaf.isConstant_of_iso Y.smallEtaleTopology (asIso (adj.counit.app G)).symm

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
