/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Topology.InverseImageModule
import WeilConjectures.Topology.InverseImageOperationExt

/-!
# Inverse image of sheaf modules and direct image

Source: Stacks Project, Sheaves, Tags 008X and 008Y
(blueprint: lem-pc-module-inverse-image-adjunction).
The inverse-image module is the landed `TopCat.Sheaf.inverseImageModule`
(the 008X structure on the explicit abelian inverse image), not Mathlib's
abstract `SheafOfModules.pullback`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopCat Opposite TopologicalSpace

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The abelian inverse-image/direct-image adjunction bijection restricts to a natural
bijection between linear morphisms `f⁻¹M ⟶ N` over `f⁻¹A` and linear morphisms
`M ⟶ f_* N` over `A`, where `A` acts on `f_* N` through the unit `η_A`.
Source: Stacks Project, Sheaves, Tags 008X and 008Y.
(blueprint: lem-pc-module-inverse-image-adjunction). -/
def moduleInverseImageAdjunctionSpec {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Y.Sheaf CommRingCat.{u}) : Prop :=
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
  let R' := (sheafCompose K (forget₂ CommRingCat RingCat)).obj
    (TopCat.Sheaf.inverseImageRing f A)
  let η : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} J K).obj R' :=
    (sheafCompose J (forget₂ CommRingCat RingCat)).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) CommRingCat.{u} J K).unit.app A)
  let adjAb := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{u} J K
  ∃ φ : ∀ (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R'),
      (TopCat.Sheaf.inverseImageModule f A M ⟶ N) ≃
        (M ⟶ (SheafOfModules.pushforward.{u} η).obj N),
    (∀ (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R')
        (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N) (V : (Opens Y)ᵒᵖ)
        (x : M.val.obj V),
      ((φ M N ψ).val.app V).hom x =
        (ψ.val.app ((Opens.map f).op.obj V)).hom
          ((adjAb.unit.app ((SheafOfModules.toSheaf R).obj M)).hom.app V x)) ∧
    (∀ (M M' : SheafOfModules.{u} R) (N : SheafOfModules.{u} R') (a : M' ⟶ M)
        (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N),
      φ M' N (TopCat.Sheaf.inverseImageModuleMap f A M' a ≫ ψ) = a ≫ φ M N ψ) ∧
    (∀ (M : SheafOfModules.{u} R) (N N' : SheafOfModules.{u} R')
        (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N) (b : N ⟶ N'),
      φ M N' (ψ ≫ b) = φ M N ψ ≫ (SheafOfModules.pushforward.{u} η).map b)

/-- The inverse-image module adjunction: the abelian adjunction restricts to linear maps,
naturally in both modules. Source: Stacks Project, Sheaves, Tags 008X and 008Y.

Proof: send a linear morphism to its abelian adjunct. The canonical unit is
semilinear, so this adjunct is linear for the action through the ring unit.
Conversely, take the inverse abelian adjunct of a linear map. Its two candidate
scalar operations commute with restriction and agree on pairs of unit images,
by semilinearity of the unit and linearity of the given map.
`TopCat.Sheaf.inverseImageOperation_ext` extends this equality to all sections,
so the inverse adjunct is linear. Faithfulness of `toSheaf` and the abelian Hom
equivalence give bijectivity and naturality in both modules; the section formula
is the defining formula of that equivalence.
(blueprint: lem-pc-module-inverse-image-adjunction). -/
theorem moduleInverseImageAdjunction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Y.Sheaf CommRingCat.{u}) : moduleInverseImageAdjunctionSpec f A := by
  classical
  -- Restrict the abelian adjunction directly; local representatives detect linearity.
  let J := Opens.grothendieckTopology Y
  let K := Opens.grothendieckTopology X
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
  let R' := (sheafCompose K (forget₂ CommRingCat RingCat)).obj
    (TopCat.Sheaf.inverseImageRing f A)
  let η : R ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} J K).obj R' :=
    (sheafCompose J (forget₂ CommRingCat RingCat)).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) CommRingCat.{u} J K).unit.app A)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{u} J K
  let forward (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R')
      (ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N) :
      M ⟶ (pushforward.{u} η).obj N :=
    ⟨PresheafOfModules.homMk
      (adj.homEquiv ((toSheaf R).obj M) ((toSheaf R').obj N)
        ((toSheaf R').map ψ)).hom (by
      intro V r m
      change (ψ.val.app ((Opens.map f).op.obj V)).hom
        ((adj.unit.app ((toSheaf R).obj M)).hom.app V (r • m)) = _
      rw [(Classical.choose_spec
        (TopCat.Sheaf.exists_inverseImageModuleInstances f A M)).2]
      exact (ψ.val.app ((Opens.map f).op.obj V)).hom.map_smul _ _)⟩
  have bijective (M : SheafOfModules.{u} R) (N : SheafOfModules.{u} R') :
      Function.Bijective (forward M N) := by
    constructor
    · intro ψ χ h
      apply (toSheaf R').map_injective
      apply (adj.homEquiv ((toSheaf R).obj M) ((toSheaf R').obj N)).injective
      exact congrArg ((toSheaf R).map) h
    · intro g
      let q : TopCat.Sheaf.inverseImageAb f A M ⟶ (toSheaf R').obj N :=
        (adj.homEquiv ((toSheaf R).obj M) ((toSheaf R').obj N)).symm
        ((toSheaf R).map g)
      have hq (V : (Opens Y)ᵒᵖ) (m : M.val.obj V) :
          q.hom.app ((Opens.map f).op.obj V)
            ((adj.unit.app ((toSheaf R).obj M)).hom.app V m) =
            (g.val.app V).hom m := by
        exact congrArg (fun (t : (toSheaf R).obj M ⟶
          ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj
            ((toSheaf R').obj N)) ↦ t.hom.app V m)
          ((adj.homEquiv ((toSheaf R).obj M) ((toSheaf R').obj N)).apply_symm_apply
            ((toSheaf R).map g))
      have linear (U : (Opens X)ᵒᵖ) (r : R'.obj.obj U)
          (m : (TopCat.Sheaf.inverseImageModule f A M).val.obj U) :
          q.hom.app U (r • m) =
            @SMul.smul _ _ (N.val.obj U).isModule.toSMul r (q.hom.app U m) := by
        apply TopCat.Sheaf.inverseImageOperation_ext f A ((toSheaf R).obj M)
          ((toSheaf R').obj N)
          (fun V r m ↦ q.hom.app V
            (@SMul.smul _ _ (TopCat.Sheaf.inverseImageModuleInstances f A M V).toSMul
              r m))
          (fun V r m ↦ @SMul.smul _ _ (N.val.obj V).isModule.toSMul
            r (q.hom.app V m))
          (by
            intro V W i r m
            rw [← NatTrans.naturality_apply q.hom i]
            exact congrArg (q.hom.app W)
              ((Classical.choose_spec
                (TopCat.Sheaf.exists_inverseImageModuleInstances f A M)).1 i r m))
          (by
            intro V W i r m
            change N.val.map i
              (@SMul.smul _ _ (N.val.obj V).isModule.toSMul r (q.hom.app V m)) = _
            exact ((N.val.map i).hom.map_smul r _).trans
              (congrArg (fun z ↦ @SMul.smul _ _ (N.val.obj W).isModule.toSMul
                (R'.obj.map i r) z) (NatTrans.naturality_apply q.hom i m).symm))
          (by
            intro V r m
            rw [← (Classical.choose_spec
              (TopCat.Sheaf.exists_inverseImageModuleInstances f A M)).2]
            rw [hq, hq]
            exact (g.val.app V).hom.map_smul r m)
          U r m
      let ψ : TopCat.Sheaf.inverseImageModule f A M ⟶ N :=
        ⟨PresheafOfModules.homMk q.hom linear⟩
      refine ⟨ψ, ?_⟩
      apply (toSheaf R).map_injective
      exact (adj.homEquiv ((toSheaf R).obj M) ((toSheaf R').obj N)).apply_symm_apply
        ((toSheaf R).map g)
  refine ⟨fun M N ↦ Equiv.ofBijective (forward M N) (bijective M N), ?_, ?_, ?_⟩
  · intro M N ψ V x
    rfl
  · intro M M' N a ψ
    apply (toSheaf R).map_injective
    exact adj.homEquiv_naturality_left ((toSheaf R).map a) ((toSheaf R').map ψ)
  · intro M N N' ψ b
    apply (toSheaf R).map_injective
    exact adj.homEquiv_naturality_right ((toSheaf R').map ψ) ((toSheaf R').map b)

end SheafOfModules
