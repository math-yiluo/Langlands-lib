/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Derived categories of modules over a quasi-coherent algebra

Source: literature/stacks-project/duality.tex, Section section-duality-finite,
Tags 0BV0 and 0AX2 (blueprint: def-pc-derived-category-qcoh-algebra).

The quasi-coherent `𝒪_Y`-algebra is the shared form `B : Y.CommAlgebraSheaf`
(`= Under Y.sheaf`) with `hB : B.toModule.IsQuasicoherent`
(def-weil-pbc-comm-algebra-sheaf, def-weil-pbc-quasi-coherent-algebra). `B`-modules are
`SheafOfModules` over the underlying ring sheaf
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj B.right`, the carrier of the
`𝒜`-modules of lem-weil-pbc-affine-module-correspondence; their underlying `𝒪_Y`-module is
the restriction of scalars along `(sheafCompose _ (forget₂ CommRingCat RingCat)).map B.hom`,
as in `Scheme.CommAlgebraSheaf.toModule`. The localization is the shared
`[HasDerivedCategory.{w} (SheafOfModules.{u} _)]` binder, as for `schemeDerivedCategory`.
-/

@[expose] public section

universe u w

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The derived category `D(B)` of sheaves of `B`-modules over a quasi-coherent
`𝒪_Y`-algebra `B`: Mathlib's `DerivedCategory` (localization of cochain complexes at the
quasi-isomorphisms, morphisms in universe `w`) of the abelian category of sheaves of modules
over the ring sheaf underlying `B`.
Source: literature/stacks-project/duality.tex, Section section-duality-finite,
Tags 0BV0 and 0AX2 (blueprint: def-pc-derived-category-qcoh-algebra). -/
abbrev sheafAlgebraDerivedCategory (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)
    (_hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        B.right))] : Type _ :=
  DerivedCategory (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj B.right))

/-- A sheaf of `B`-modules is a quasi-coherent `B`-module when its underlying `𝒪_Y`-module
(restriction of scalars along the structure morphism `𝒪_Y → B`) is quasi-coherent.
Source: literature/stacks-project/duality.tex, Section section-duality-finite,
Tags 0BV0 and 0AX2 (blueprint: def-pc-derived-category-qcoh-algebra). -/
def sheafAlgebraModuleIsQuasiCoherent (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)
    (_hB : B.toModule.IsQuasicoherent)
    (M : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        B.right)) : Prop :=
  ((SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
      B.hom)).obj M).IsQuasicoherent

/-- An object `K` of `D(B)` lies in `D⁺_QCoh(B)`: its cohomology sheaves vanish below some
integer `n`, and every cohomology sheaf is a quasi-coherent `B`-module.
Source: literature/stacks-project/duality.tex, Section section-duality-finite,
Tags 0BV0 and 0AX2 (blueprint: def-pc-derived-category-qcoh-algebra). -/
def sheafAlgebraDerivedQCohProperty (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)
    (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        B.right))] :
    ObjectProperty (sheafAlgebraDerivedCategory Y B hB) :=
  fun K =>
    (∃ n : ℤ, ∀ m : ℤ, m < n →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
          B.right)) m).obj K)) ∧
      ∀ m : ℤ,
        sheafAlgebraModuleIsQuasiCoherent Y B hB
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
            ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
              B.right)) m).obj K)

/-- The full subcategory `D⁺_QCoh(B)` of `D(B)`.
Source: literature/stacks-project/duality.tex, Section section-duality-finite,
Tags 0BV0 and 0AX2 (blueprint: def-pc-derived-category-qcoh-algebra). -/
abbrev sheafAlgebraDerivedQCohCategory (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)
    (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        B.right))] : Type _ :=
  (sheafAlgebraDerivedQCohProperty Y B hB).FullSubcategory

end AlgebraicGeometry
