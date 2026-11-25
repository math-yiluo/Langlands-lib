/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)

private lemma stalk_range_congr
    {Y : Scheme.{u}} {g₁ g₂ : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (hg : g₁ = g₂) (sq₁ : IsPullback e h g₁ p) (sq₂ : IsPullback e h g₂ p)
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (baseChangeHomologyMap Λ sq₁ q G)).hom =
    Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
      (baseChangeHomologyMap Λ sq₂ q G)).hom := by
  subst hg
  rfl

/-- Target restriction sends the image of base change into the image of base change.

Source: the commutative restriction square in Stacks Tag 0F07.
(blueprint: lem-sbc-target-stalk-restriction-image)

Proof: use compatibility of base change with target and source transitions. Compose
with the inverse-image composition isomorphism, and use naturality of base change in
that coefficient morphism. This gives a commuting square on stalks. The two expressions
for the structure morphism agree by associativity, so their base-change ranges agree.
The source transition followed by the coefficient comparison supplies the preimage.
-/
theorem baseChangeTargetStalkMap_mem_range {U V : Over T} (φ : U ⟶ V)
    (η : baseChangeSourceStalk Λ p g q F x V) :
    (baseChangeTargetStalkMap Λ p g q F x φ).hom
      ((baseChangeStalkMap Λ p g q F x V).hom η) ∈
        Set.range (baseChangeStalkMap Λ p g q F x U).hom := by
  obtain ⟨TU, uU, πU⟩ := U
  obtain ⟨TV, uV, πV⟩ := V
  have hw := Over.w φ
  obtain ⟨f, r, w⟩ := φ
  change TU ⟶ TV at f
  change uU ⟶ uV at r
  change f ≫ πV = πU at hw
  subst πU
  let eV := pullback.fst (πV ≫ g) p
  let hV := pullback.snd (πV ≫ g) p
  let eU := pullback.fst ((f ≫ πV) ≫ g) p
  let hU := pullback.snd ((f ≫ πV) ≫ g) p
  have sqV : IsPullback eV hV (πV ≫ g) p := IsPullback.of_hasPullback _ _
  have sqU : IsPullback eU hU (f ≫ (πV ≫ g)) p := by
    have hs : IsPullback eU hU ((f ≫ πV) ≫ g) p := IsPullback.of_hasPullback _ _
    exact Eq.mp (congrArg (fun k ↦ IsPullback eU hU k p) (Category.assoc f πV g)) hs
  let a := pullback.lift (eU ≫ f) hU
    (by
      calc
        (eU ≫ f) ≫ (πV ≫ g) = eU ≫ ((f ≫ πV) ≫ g) := by
          simp only [Category.assoc]
        _ = hU ≫ p := pullback.condition)
  let ν := (upperStarComp (ModuleCat.{u + 1} Λ) f πV (f ≫ πV) rfl).inv.app F
  have hc := baseChangeHomologyMap_comp_baseChangeTargetTransition Λ sqV q f sqU a
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (((πV)^*[ModuleCat.{u + 1} Λ]).obj F)
  have hn := baseChangeHomologyMap_naturality Λ sqU q ν
  have hc' := congrArg (fun k ↦ k ≫ (baseChangeTargetFunctor Λ eU hU q).map ν) hc
  have hn' := congrArg (fun k ↦ baseChangeSourceTransition Λ p (πV ≫ g) q f
    (((πV)^*[ModuleCat.{u + 1} Λ]).obj F) ≫ k) hn
  have hb := (Category.assoc _ _ _).symm.trans
    (hc'.trans ((Category.assoc _ _ _).trans
      (hn'.trans (Category.assoc _ _ _).symm)))
  have hb' := congrArg (fun z ↦ ModuleCat.Hom.hom
    ((X.uliftPointSmallEtale x).sheafFiber.map z)) hb
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hb'
  have hη := LinearMap.congr_fun hb' η
  simp only [LinearMap.coe_comp, Function.comp_apply] at hη
  unfold baseChangeStalkMap
  rw [stalk_range_congr Λ p q x (Category.assoc f πV g)
    (IsPullback.of_hasPullback ((f ≫ πV) ≫ g) p) sqU
    (((f ≫ πV)^*[ModuleCat.{u + 1} Λ]).obj F)]
  unfold baseChangeTargetStalkMap
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact ⟨_, hη.symm⟩

end AlgebraicGeometry.Etale
