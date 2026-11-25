/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapCompositeStageTail
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageTransport
import WeilConjectures.AlgebraicGeometry.PerfectOverlapCompositeStageMap
import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport

/-! # A component of composite overlap compatibility
Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
private theorem factorComponent {𝒟 : Type*} [Category 𝒟]
    {P Q R S : 𝒟} (stage : P ⟶ S) (counit : P ⟶ Q) (eta : P ⟶ R)
    (transport : Q ≅ R) (tail : Q ⟶ S)
    (hstage : stage = counit ≫ tail) (heta : eta = counit ≫ transport.hom) :
    stage = eta ≫ transport.inv ≫ tail := by
  rw [hstage, heta]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option linter.unusedVariables false in
/-- Factoring the constructed stage map through the prescribed natural comparison.
Source: Stacks Project, Tag 08DW, compatibility of restriction with pullback.

Proof: First rewrite the endpoint stage functors by their proved equations,
so the stage transport is the fixed derived transport. On either Boolean branch
expand the stage-map constructor. Its first
factor is the stage pullback of the open-site counit, and the remaining
factors are the explicitly constructed tail. The component formula
`perfectOverlapNaturalComparisonOfSquare_hom_app` writes eta as that same
counit followed by the derived transport. Postcomposing eta with the inverse
transport cancels the transport by the isomorphism identities. Associativity
then gives precisely the displayed factorization. The two presentations of
an inverse-image intersection agree by `Scheme.Hom.preimage_inf`; their
inclusion proofs agree by proof irrelevance. No nonemptiness is used.
(blueprint: lem-pc-perfect-overlap-composite-counit-factor). -/
theorem perfectOverlapCompositeCounitFactor
    {X Y K C T S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (l : Over.mk b ⟶ Over.mk q)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let s := W.ι ≫ pY
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let m := baseChangeMap s l
  let eY := ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let eK := ((isPullback_morphismRestrict f W).paste_vert hf).isoPullback
  ∀ hmap : eY.inv ≫ r = m ≫ eK.inv,
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let η := perfectOverlapNaturalComparisonOfSquare g f pX pK pY b q hg hf U V r m hmap
  let σ : ∀ a : Bool,
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor.obj (F a) ≅
        (derivedPullback (pullback.fst s q)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      ((perfectOverlapStageObjectIso f pK pY q hf U V U inf_le_left).app A)
      ((perfectOverlapStageObjectIso f pK pY q hf U V V inf_le_right).app B)
  let D : ∀ a : Bool,
      (perfectOverlapStageEquivalence g pX pY b hg U V).functor.obj
          ((derivedPullback r).obj (F a)) ⟶
        (derivedPullback (pullback.fst s b)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      (perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V U inf_le_left A)
      (perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V V inf_le_right B)
  ∀ a : Bool,
    perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV a =
      η.hom.app (F a) ≫
        (perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).inv.app (F a) ≫ D a
    := by
  intro W s r m eY eK hmap data F apex η σ D a
  let site : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ W)) ≌
      SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ W).toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv _
  let counit := (perfectOverlapStageEquivalence g pX pY b hg U V).functor.map
    (site.mapDerivedCategory.counitIso.hom.app ((derivedPullback r).obj (F a)))
  have hstage :
      perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV a =
        counit ≫ D a := by
    cases a
    · refine (perfectOverlapCompositeStageMap_false f gk g hgf pX pY b hg U V A B E
        φU φV).trans ?_
      dsimp only [F, D, counit, Bool.false_eq_true, ↓reduceIte]
      unfold perfectOverlapCompositeStageMapAt perfectOverlapCompositeStageTailAt
      rfl
    · refine (perfectOverlapCompositeStageMap_true f gk g hgf pX pY b hg U V A B E
        φU φV).trans ?_
      dsimp only [F, D, counit, ↓reduceIte]
      unfold perfectOverlapCompositeStageMapAt perfectOverlapCompositeStageTailAt
      rfl
  have heta : η.hom.app (F a) = counit ≫
      (perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).hom.app
        (F a) := by
    unfold perfectOverlapStageTransport
    exact perfectOverlapNaturalComparisonOfSquare_hom_app g f pX pK pY b q hg hf
      U V r m hmap (F a)
  exact factorComponent _ counit _
    ((perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).app (F a))
    (D a) hstage heta

end AlgebraicGeometry
