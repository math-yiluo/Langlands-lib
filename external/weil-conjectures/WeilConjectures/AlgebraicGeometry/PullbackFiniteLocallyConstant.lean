/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLift
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Pullback of finite locally constant abelian etale sheaves

Source: Stacks Project, Tags 095A, 03Q1 (3), and 03CB
(blueprint: lem-weil-pbc-pullback-finite-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem underlying_isConstant_over_iff {X : Scheme.{u}} (U : X.Etale)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Sheaf.IsConstant (X.smallEtaleTopology.over U)
      (((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U) ↔
    Sheaf.IsConstant U.left.smallEtaleTopology
      ((sheafCompose U.left.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} U.hom).obj G)) := by
  let e := (sheafCompose U.left.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
    (overSheafEquivFunctorObjOverIso AddCommGrpCat.{u + 1} U G)
  rw [← Sheaf.isConstant_sheafCongr_functor_iff (J := X.smallEtaleTopology.over U)
    (K := U.left.smallEtaleTopology) (Etale.overEquiv U) Over.mkIdTerminal]
  constructor
  · intro h
    have : Sheaf.IsConstant U.left.smallEtaleTopology ((sheafCompose U.left.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.overSheafEquiv U AddCommGrpCat.{u + 1}).functor.obj (G.over U))) := h
    exact Sheaf.isConstant_congr _ e
  · intro h
    have := h
    exact Sheaf.isConstant_congr _ e.symm

private theorem underlying_isConstant_upperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Sheaf.IsConstant X.smallEtaleTopology
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) :
    Sheaf.IsConstant Y.smallEtaleTopology
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj G)) := by
  have hL : CategoryTheory.Limits.PreservesFiniteLimits (etaleSetPullback g) := by
    unfold etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, hea⟩ := etaleInverseImageAbelianLift Y X g hL
  clear hea
  let S := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  have : S.IsConstant X.smallEtaleTopology := hG
  let hT := MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) X
  have hc := Sheaf.isConstant_sheafPullback (K := Y.smallEtaleTopology)
    g.Etale hT (hT.isTerminalObj g.Etale) S
  let e := (Functor.sheafPullbackConstruction.sheafPullbackIso
    g.Etale
    (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology).app S
  have hconst : ((etaleSetPullback g).obj S).IsConstant Y.smallEtaleTopology :=
    Sheaf.isConstant_congr _ e
  exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _ (ea.app G).symm hconst

private theorem underlying_locallyConstant_upperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) :
    IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj G)) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰.pullback₂ g, fun j ↦ ?_⟩
  rw [underlying_isConstant_over_iff]
  have h₁ := (underlying_isConstant_over_iff (𝒰.etalePrecoverageToEtale j) G).mp (h𝒰 j)
  have h₂ := underlying_isConstant_upperStar (CategoryTheory.Limits.pullback.fst (𝒰.f j) g)
    ((Etale.upperStar AddCommGrpCat.{u + 1} (𝒰.f j)).obj G) h₁
  let e := ((Etale.upperStarComp AddCommGrpCat.{u + 1}
      (CategoryTheory.Limits.pullback.fst (𝒰.f j) g) (𝒰.f j)).app G).symm ≪≫
    eqToIso (congrArg (fun m ↦ (Etale.upperStar AddCommGrpCat.{u + 1} m).obj G)
      CategoryTheory.Limits.pullback.condition) ≪≫
    (Etale.upperStarComp AddCommGrpCat.{u + 1}
      (CategoryTheory.Limits.pullback.snd (𝒰.f j) g) g).app G
  have hconst : Sheaf.IsConstant (CategoryTheory.Limits.pullback (𝒰.f j) g).smallEtaleTopology
      ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1}
          (CategoryTheory.Limits.pullback.fst (𝒰.f j) g)).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (𝒰.f j)).obj G))) := h₂
  change Sheaf.IsConstant (CategoryTheory.Limits.pullback (𝒰.f j) g).smallEtaleTopology _
  exact @Sheaf.isConstant_congr _ _ _ _ _ _ _ _
    ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e) hconst

private theorem finiteLocallyConstant_of_iso {X : Scheme.{u}}
    {G H : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : G ≅ H)
    (hG : IsFiniteLocallyConstantSheafOfTypes G) :
    IsFiniteLocallyConstantSheafOfTypes H := by
  obtain ⟨⟨𝒰, h𝒰⟩, hf⟩ := hG
  refine ⟨⟨𝒰, fun j ↦ ?_⟩, ?_⟩
  · have := h𝒰 j
    exact Sheaf.isConstant_congr _ ((X.smallEtaleTopology.overPullback _ _).mapIso e)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
    have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
      (hf.isFinitelyGenerated_sheafFiber Ω s)
    exact Finite.of_equiv _ (((pointSmallEtale s).sheafFiber.mapIso e).toEquiv)

/-- Pullback along a composite agrees with iterated pullback, and preserves finite local
constancy of the underlying sheaf of sets. Source: Stacks Project, Tags 095A, 03Q1 (3),
and 03CB (blueprint: lem-weil-pbc-pullback-finite-locally-constant).

Proof:
1. `Etale.upperStarComp` identifies composite and iterated inverse images.
2. The equivalence from the localized etale site at U to the etale site of U,
   followed by forgetting abelian groups, identifies the restriction of the underlying
   set sheaf with the underlying set sheaf of pullback along U.hom.
3. Forgetting abelian groups commutes with inverse image by
   `etaleInverseImageAbelianLift`, using left exactness of set pullback.
   The generic constant-sheaf pullback comparison
   applies to base change, which preserves terminal objects. Thus pullback preserves
   constancy of the underlying set sheaf, without any small-universe assumption on its
   constant value.
4. Pull back the trivializing etale cover. For each member, the two composition
   isomorphisms and the pullback-square equation identify its restriction with the
   pullback of the original constant restriction. This proves local constancy.
5. `Etale.upperStarCompSheafFiberIso` identifies the abelian stalks. On both sides,
   `Point.sheafFiberCompIso` for the forgetful functor identifies their underlying sets
   with the set-valued stalks. Transport finiteness across this composite isomorphism.
6. Both local constancy and finite stalks are invariant under isomorphism: restrict the
   isomorphism to each cover member and apply each geometric fiber functor. Transport
   along the inverse of the composition isomorphism from step 1 -/
theorem pullback_finite_locally_constant {T Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (f : Y ⟶ T) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) :
    Nonempty (((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F) ≅
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))) ∧
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y'.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (g ≫ f)).obj F)) := by
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} f).obj F
  let c := (Etale.upperStarComp AddCommGrpCat.{u + 1} g f).app F
  refine ⟨⟨c⟩, finiteLocallyConstant_of_iso
    ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso c.symm) ?_⟩
  refine ⟨underlying_locallyConstant_upperStar g G hF.1, ?_⟩
  refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
  have hfinite : Finite (((pointSmallEtale (s ≫ g)).sheafFiber
      (A := Type (u + 1))).obj
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) :=
    hF.finite_sheafFiber Ω (s ≫ g)
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let e := ((pointSmallEtale s).sheafFiberCompIso (CategoryTheory.forget AddCommGrpCat.{u + 1})).app
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj G) ≪≫
    (CategoryTheory.forget AddCommGrpCat.{u + 1}).mapIso
      ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g s).app G) ≪≫
    (((pointSmallEtale (s ≫ g)).sheafFiberCompIso
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app G).symm
  exact @Finite.of_equiv _ _ hfinite e.toEquiv.symm

end AlgebraicGeometry.Scheme
