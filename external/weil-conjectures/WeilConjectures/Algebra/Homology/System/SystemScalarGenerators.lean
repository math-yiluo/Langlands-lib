/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # Local generators for normalized scalar extension

Source: Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S} (A : SystemScalarModel φ)

/-- Maps out of scalar extension agree if they agree on all local unit tensors.
Source: Stacks 03D7 and 03EK (blueprint: lem-pur-system-scalar-generators).
Proof: apply the injective scalar Hom correspondence. Its transpose evaluates a map
on the normalized adjunction unit, namely one tensor x. Equality of these section maps
is equality of the transposed module-sheaf morphisms. -/
theorem systemScalarModel_hom_ext
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (M : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f g : A.model.E.obj P ⟶ M)
    (h : ∀ U x, f.val.app U (systemModelTmul A.model P U 1 x) =
      g.val.app U (systemModelTmul A.model P U 1 x)) : f = g := by
  apply (A.ordinaryAdj.homEquiv P M).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change f.val.app U ((A.ordinaryAdj.unit.app P).val.app U x) =
    g.val.app U ((A.ordinaryAdj.unit.app P).val.app U x)
  rw [A.unit_normalized]
  exact h U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar-extension maps send c tensor x to c tensor the image of x.
Source: Stacks 03EK (blueprint: lem-pur-system-scalar-generators).
Proof: naturality of the adjunction identifies the transpose of extension of f with
f followed by the unit. Apply the normalized pure-tensor transpose formula and use
linearity and the unit normalization. -/
theorem systemScalarModel_map_tmul
    {P Q : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)}
    (f : P ⟶ Q) (U : Cᵒᵖ) (c : S.obj.obj U) (x : P.val.obj U) :
    (A.model.E.map f).val.app U (systemModelTmul A.model P U c x) =
      systemModelTmul A.model Q U c (f.val.app U x) := by
  have hn : A.ordinaryAdj.homEquiv P (A.model.E.obj Q) (A.model.E.map f) =
      f ≫ A.ordinaryAdj.unit.app Q := by
    have h := A.ordinaryAdj.homEquiv_naturality_left f (𝟙 (A.model.E.obj Q))
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using h
  rw [systemScalarModel_transpose_tmul, hn]
  have hu := A.unit_normalized Q U (f.val.app U x)
  dsimp only [systemModelTmul] at hu ⊢
  rw [one_smul] at hu
  exact congrArg (fun y : (A.model.E.obj Q).val.obj U ↦
    (c • y : (A.model.E.obj Q).val.obj U)) hu

end SheafOfModules
