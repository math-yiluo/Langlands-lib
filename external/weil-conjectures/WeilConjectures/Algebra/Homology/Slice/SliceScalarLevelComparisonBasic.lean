/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearSliceScalarGeneratorsBasic

/-! # Data of the scalar level comparison

The existing coefficient-linear comparison API, separated from its construction.
Source: Stacks Project, Modules on Sites, Tags 0E8I, 03DI, 03CY and 03EK.
(blueprint: def-sf-slice-scalar-level-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r
open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{max c v r}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})
  (α : (Functor.const ℕᵒᵖ).obj O ⟶ B)
  (AX : SliceScalarTowerPresentation.{c, v, r} O B α)
  (AV : SliceScalarTowerPresentation.{max c v, v, r} (O.over U)
    (sliceScalarRings.{c, v, r} B U) (sliceScalarAlgebra.{c, v, r} B U O α))
  (extension : SliceSystemExtensionPresentation.{c, v, r} B U)

/-- Transport a level comparison along the specified object identifications.
Source: Stacks 03EK (blueprint: def-sf-slice-scalar-level-comparison-data). -/
def sliceScalarComponentHom
    (e : ∀ G n,
      changeOfRings.{v, c, max c v r} (α.app (op n))
        ((localizedSystemExtension.{c, v, r} O U).obj G) ≅
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)) (G) (n : ℕ) :
    (AX.F.obj ((localizedSystemExtension.{c, v, r} O U).obj G)).level n ⟶
      (extension.F.obj (AV.F.obj G)).level n :=
  eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n) ≫
    (e G n).hom ≫
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map
        (eqToHom (AV.obj_eq G n).symm) ≫
          eqToHom (extension.obj_eq (AV.F.obj G) n).symm

/-- Levelwise scalar projection formula and its generator equations, prior to assembling
an isomorphism of strict systems or complexes.
Source: Stacks 0E8I, 03DI, 03CY and 03EK
(blueprint: def-sf-slice-scalar-level-comparison-data). -/
structure SliceScalarLevelComparison where
  /-- Its coefficient-linear component on the actual sheafified tensor objects. -/
  component : ∀ G n,
    changeOfRings.{v, c, max c v r} (α.app (op n))
      ((localizedSystemExtension.{c, v, r} O U).obj G) ≅
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)
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
  /-- The forward level maps commute with every coefficient transition. -/
  transition : ∀ G {m n : ℕ} (h : m ≤ n),
    sliceScalarComponentHom B U O α AX AV extension component G n ≫
        (extension.F.obj (AV.F.obj G)).transition h =
      (AX.F.obj ((localizedSystemExtension.{c, v, r} O U).obj G)).transition h ≫
        (systemRestriction B h).map
          (sliceScalarComponentHom B U O α AX AV extension component G m)
  /-- Naturality of the forward maps at each coefficient level. -/
  naturality : ∀ {G G'} (g : G ⟶ G') n,
    (AX.F.map ((localizedSystemExtension.{c, v, r} O U).map g)).app n ≫
        sliceScalarComponentHom B U O α AX AV extension component G' n =
      sliceScalarComponentHom B U O α AX AV extension component G n ≫
        (extension.F.map (AV.F.map g)).app n

end SheafOfModules
