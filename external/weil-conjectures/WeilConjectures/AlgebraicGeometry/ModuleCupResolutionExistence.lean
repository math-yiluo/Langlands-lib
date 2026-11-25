/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupRealizationComplexData
import WeilConjectures.AlgebraicGeometry.ModuleCupComponentSectionMap
import WeilConjectures.AlgebraicGeometry.ModuleCupComponentChainEquation

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  globalPullbackMatesColimits cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

/-- Component maps and the signed chain equation obtained by sheafifying the pairing.
This is the assembly statement before packaging the components as a morphism of complexes.
Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-components) -/
def CupResolutionPairing.ComponentData {F G : X.Modules} (D : CupResolutionPairing F G) :=
  ∃ l : ∀ n : ℤ, (D.left.integerComplex ⊗ D.right.integerComplex).X n ⟶
      D.target.integerComplex.X n,
    (∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V))
      (b : Γ(D.right.K.X q, V)),
      ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega)) ≫ l (p + q) ≫
        (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)) =
        D.pair p q V a b) ∧
    (∀ (i j : ℤ), ComplexShape.up ℤ |>.Rel i j →
      l i ≫ D.target.integerComplex.d i j =
        (D.left.integerComplex ⊗ D.right.integerComplex).d i j ≫ l j)

/-- The component assembly from restriction-compatible bilinear maps and Leibniz.
Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-components)
Proof: in each bidegree apply the sheaf tensor universal property to the section pairing,
then use the coproduct universal property of the total tensor. The Leibniz identity gives
the displayed chain equation; negative summands are zero by extension. -/
theorem moduleCup_component_data_exists {F G : X.Modules} (D : CupResolutionPairing F G) :
    D.ComponentData := by
  obtain ⟨l, hl⟩ := moduleCup_component_section_map_exists D
  exact ⟨l, hl, moduleCup_component_chain_equation D l hl⟩

/-- A cochain realization exists.
Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
Proof: use the sheaf tensor universal property to descend the restriction-compatible
bilinear section maps in each nonnegative bidegree. Assemble these maps on the coproduct
terms of the total tensor. The Leibniz identity gives the differential compatibility.
Negative-degree factors are zero, so extend those summands by zero. The coproduct
inclusion formula is exactly the section formula in Realizes.
(blueprint: lem-sc-module-cup-resolution-existence) -/
theorem moduleCup_resolution_realization_exists {F G : X.Modules} (D : CupResolutionPairing F G) :
    ∃ t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex,
      D.Realizes t := by
  obtain ⟨l, hl, hchain⟩ := moduleCup_component_data_exists D
  let t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex :=
    HomologicalComplex.Hom.mk l hchain
  refine ⟨t, ?_⟩
  intro p q V a b
  exact hl p q V a b


end
end AlgebraicGeometry.Scheme.Modules
