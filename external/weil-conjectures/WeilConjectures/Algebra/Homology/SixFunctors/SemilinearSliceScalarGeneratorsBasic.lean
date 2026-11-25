/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import Mathlib.Algebra.Homology.Additive

/-! # Scalar comparison on generators of strict semilinear slice systems

Source: Stacks Project, Modules on Sites, Tags 0E8I, 03DI, 03CY and 03EK;
Sites, Tag 00WK. The coefficient-generator refinement is described in the DAG proof.
(blueprint: def-sf-semilinear-slice-scalar-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r

open CategoryTheory Opposite
open scoped ChangeOfRings

attribute [local implicit_reducible] CategoryTheory.sheafCompose

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The pure section `x tensor b` in actual sheafified extension of scalars.
The existing change-of-rings construction places the coefficient first, so this is
represented by `b tensor x` before sheafification.
Source: Stacks 03EK (blueprint: lem-sf-semilinear-slice-scalar-generators). -/
def sliceScalarPure {O B : Sheaf J CommRingCat.{max c v r}} (α : O ⟶ B)
    (H : ringedSiteModules.{max c v r}
      (derivedChangeRingIndependentCoefficients.{max c v r, c, v} J O))
    (W : Cᵒᵖ) (x : H.val.obj W) (b : B.obj.obj W) :
    (changeOfRings.{v, c, max c v r} α H).val.obj W :=
  ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
    (𝟙 (derivedChangeRingIndependentCoefficients.{max c v r, c, v} J B).obj)).unit.app
      (changeOfRingsPresheaf.{v, c, max c v r} α H)).app W
        (b ⊗ₜ[O.obj.obj W, (α.hom.app W).hom] x)

/-- The existing coefficient tower restricted termwise to the localized site.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-slice-scalar-generators). -/
abbrev sliceScalarRings (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C) :=
  B ⋙ J.overPullback CommRingCat.{max c v r} U

/-- A presentation of the specified scalar-extension tower functor, including its
actual level objects and maps, all pure-tensor transitions and the scalar-unit
augmentation. This is result data, not a hypothesis supplying a scalar comparison.
Source: Stacks 03EK, 03CZ (blueprint: lem-sf-semilinear-slice-scalar-generators). -/
structure SliceScalarTowerPresentation (O : Sheaf J CommRingCat.{max c v r})
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj O ⟶ B) where
  /-- Termwise extension of scalars with the prescribed strict transitions. -/
  F : ringedSiteModules.{max c v r}
    (derivedChangeRingIndependentCoefficients.{max c v r, c, v} J O) ⥤
    StrictRingSystem.{c, v, max c v r} B
  /-- No replacement of the level objects. -/
  obj_eq : ∀ H n, (F.obj H).level n = changeOfRings.{v, c, max c v r} (α.app (op n)) H
  /-- The actual sheafification of `id tensor f`. -/
  map_eq : ∀ {H H'} (f : H ⟶ H') n,
    (F.map f).app n = eqToHom (obj_eq H n) ≫
      changeOfRingsHom.{v, c, max c v r} (α.app (op n)) H f ≫ eqToHom (obj_eq H' n).symm
  /-- All iterated transitions act by the coefficient transition on pure tensors. -/
  transition_pure : ∀ H {m n : ℕ} (h : m ≤ n) (W : Cᵒᵖ)
    (x : H.val.obj W) (b : (B.obj (op n)).obj.obj W),
    (eqToHom (obj_eq H m)).val.app W
        (((F.obj H).transition h).val.app W
          ((eqToHom (obj_eq H n).symm).val.app W
            (sliceScalarPure.{c, v, r} (α.app (op n)) H W x b))) =
      sliceScalarPure.{c, v, r} (α.app (op m)) H W x
        ((B.map (homOfLE h).op).hom.app W b)
  /-- Units are morphisms of ordinary O-module towers. -/
  unit : ∀ H n, H ⟶ (restrictScalars
    ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map (α.app (op n)))).obj
      ((F.obj H).level n)
  /-- The actual insertion of one, after the sheafification unit. -/
  unit_pure : ∀ H n (W : Cᵒᵖ) (x : H.val.obj W),
    (eqToHom (obj_eq H n)).val.app W ((unit H n).val.app W x) =
      sliceScalarPure.{c, v, r} (α.app (op n)) H W x 1
  /-- Compatibility of both scalar-unit augmentations with every transition. -/
  unit_transition : ∀ H {m n : ℕ} (h : m ≤ n) (W : Cᵒᵖ) (x : H.val.obj W),
    ((F.obj H).transition h).val.app W ((unit H n).val.app W x) =
      (unit H m).val.app W x
  /-- The construction applies degreewise to arbitrary unbounded complexes. -/
  [additive : F.Additive]

attribute [instance] SliceScalarTowerPresentation.additive

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The termwise extension functor on strict systems, fixed on every original
extension summand, including transitions and maps between systems.
Source: Stacks 03DI, 03CY (blueprint: lem-sf-semilinear-slice-scalar-generators). -/
structure SliceSystemExtensionPresentation where
  /-- Extension of each coefficient module before forgetting scalars. -/
  F : StrictRingSystem.{max c v, v, max c v r} (sliceScalarRings.{c, v, r} B U) ⥤
    StrictRingSystem.{c, v, max c v r} B
  /-- These are the prescribed direct-sum extensions followed by sheafification. -/
  obj_eq : ∀ M n, (F.obj M).level n =
    (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj (M.level n)
  /-- Module morphisms are extended by the actual extension functor. -/
  map_eq : ∀ {M N} (f : M ⟶ N) n,
    (F.map f).app n = eqToHom (obj_eq M n) ≫
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map (f.app n) ≫
        eqToHom (obj_eq N n).symm
  /-- On every original summand the system transition extends that of M. -/
  transition_generator : ∀ M {m n : ℕ} (h : m ≤ n) (W : Over U)
    (x : (M.level n).val.obj (op W)),
    (eqToHom (obj_eq M m)).val.app (op W.left)
        (((F.obj M).transition h).val.app (op W.left)
          ((eqToHom (obj_eq M n).symm).val.app (op W.left)
            (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U (M.level n) W x))) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op m)) U (M.level m) W
        ((M.transition h).val.app (op W) x)
  /-- Extension is additive, so its application to complexes is defined. -/
  [additive : F.Additive]

attribute [instance] SliceSystemExtensionPresentation.additive

/-- Restriction of the O-algebra structure, with the canonical constant-functor transport.
Source: Stacks 03DI, 03CZ (blueprint: lem-sf-semilinear-slice-scalar-generators). -/
def sliceScalarAlgebra (O : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj O ⟶ B) :
    (Functor.const ℕᵒᵖ).obj (O.over U) ⟶ sliceScalarRings.{c, v, r} B U :=
  (Functor.constComp ℕᵒᵖ O (J.overPullback CommRingCat.{max c v r} U)).inv ≫
    Functor.whiskerRight α (J.overPullback CommRingCat.{max c v r} U)

/-- The full generator-normalized comparison, including its construction on strict
systems before forgetting coefficients. All fields are asserted to exist by the
statement below; none is an extra input hypothesis.
Source: Stacks 0E8I, 03DI, 03CY, 03EK, refined as in the DAG proof
(blueprint: lem-sf-semilinear-slice-scalar-generators). -/
structure SemilinearSliceScalarGenerators (O : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj O ⟶ B) where
  /-- A_X on the actual modules, with strict coefficient transitions. -/
  AX : SliceScalarTowerPresentation.{c, v, r} O B α
  /-- A_V on the actual slice modules. -/
  AV : SliceScalarTowerPresentation.{max c v, v, r} (O.over U)
    (sliceScalarRings.{c, v, r} B U) (sliceScalarAlgebra.{c, v, r} B U O α)
  /-- Termwise extension with each coefficient action retained. -/
  extension : SliceSystemExtensionPresentation.{c, v, r} B U
  /-- The natural isomorphism in S(B), not merely after scalar restriction. -/
  comparison : localizedSystemExtension.{c, v, r} O U ⋙ AX.F ≅ AV.F ⋙ extension.F
  /-- Its coefficient-linear component on the actual sheafified tensor objects. -/
  component : ∀ G n,
    changeOfRings.{v, c, max c v r} (α.app (op n))
      ((localizedSystemExtension.{c, v, r} O U).obj G) ≅
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)
  /-- Equality with evaluation of the strict system isomorphism. -/
  component_eq : ∀ G n,
    (comparison.hom.app G).app n =
      eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n) ≫
        (component G n).hom ≫
          (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map
            (eqToHom (AV.obj_eq G n).symm) ≫
              eqToHom (extension.obj_eq (AV.F.obj G) n).symm
  /-- The prescribed forward formula after both sheafifications. -/
  generator : ∀ G n (W : Over U) (x : G.val.obj (op W))
    (b : (B.obj (op n)).obj.obj (op W.left)),
    (component G n).hom.val.app (op W.left)
        (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
          (ringedSliceExtensionSection.{c, v, r} O U G W x) b) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U _ W
        (sliceScalarPure.{max c v, v, r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b)
  /-- Generator normalization uniquely specifies the B_n-linear realization. -/
  unique : ∀ G n (f :
    changeOfRings.{v, c, max c v r} (α.app (op n))
      ((localizedSystemExtension.{c, v, r} O U).obj G) ⟶
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)),
    (∀ (W : Over U) (x : G.val.obj (op W))
      (b : (B.obj (op n)).obj.obj (op W.left)),
      f.val.app (op W.left)
          (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
            (ringedSliceExtensionSection.{c, v, r} O U G W x) b) =
        ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U _ W
          (sliceScalarPure.{max c v, v, r}
            ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b)) →
      f = (component G n).hom
  /-- The inverse formula uses exactly the same original generators. -/
  inverse_generator : ∀ G n (W : Over U) (x : G.val.obj (op W))
    (b : (B.obj (op n)).obj.obj (op W.left)),
    (component G n).inv.val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U _ W
          (sliceScalarPure.{max c v, v, r}
            ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b)) =
      sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
        (ringedSliceExtensionSection.{c, v, r} O U G W x) b
  /-- The common underlying O-module identification of the two extensions. -/
  scalarIdentification : ∀ n F,
    (localizedSystemExtension.{c, v, r} O U).obj
      ((restrictScalars ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).obj F) ≅
      (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        (α.app (op n)))).obj
          ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj F)
  /-- This identification preserves each original direct-sum injection. -/
  scalarIdentification_generator : ∀ n F (W : Over U) (x : F.val.obj (op W)),
    (scalarIdentification n F).hom.val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} O U _ W x) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x
  /-- No other identification preserving all original summands is permitted. -/
  scalarIdentification_unique : ∀ n F (f :
    (localizedSystemExtension.{c, v, r} O U).obj
      ((restrictScalars ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).obj F) ⟶
      (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        (α.app (op n)))).obj
          ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj F)),
    (∀ (W : Over U) (x : F.val.obj (op W)),
      f.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} O U _ W x) =
        ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x) →
      f = (scalarIdentification n F).hom
  /-- The two scalar-unit insertions form the required square of O-module sheaf maps. -/
  augmentation : ∀ G n,
    AX.unit ((localizedSystemExtension.{c, v, r} O U).obj G) n ≫
        (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
          (α.app (op n)))).map
            (eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n) ≫
              (component G n).hom) =
      (localizedSystemExtension.{c, v, r} O U).map
        (AV.unit G n ≫
          (restrictScalars ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
            ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).map
              (eqToHom (AV.obj_eq G n))) ≫
        (scalarIdentification n _).hom
  /-- The unbounded chain comparison is the degreewise lift of this very isomorphism. -/
  chain : (localizedSystemExtension.{c, v, r} O U ⋙ AX.F).mapHomologicalComplex (.up ℤ) ≅
    (AV.F ⋙ extension.F).mapHomologicalComplex (.up ℤ)
  /-- Its degree-i morphism is the comparison for G^i, as a strict system morphism. -/
  chain_degree : ∀ (G : CochainComplex (ringedSiteModules.{max c v r}
    (derivedChangeRingIndependentCoefficients.{max c v r, max c v, v}
      (J.over U) (O.over U))) ℤ) (i : ℤ),
    (chain.hom.app G).f i = comparison.hom.app (G.X i)
  /-- The inverse chain comparison is degreewise the inverse strict comparison. -/
  chain_inverse_degree : ∀ (G : CochainComplex (ringedSiteModules.{max c v r}
    (derivedChangeRingIndependentCoefficients.{max c v r, max c v, v}
      (J.over U) (O.over U))) ℤ) (i : ℤ),
    (chain.inv.app G).f i = comparison.inv.app (G.X i)

end SheafOfModules
