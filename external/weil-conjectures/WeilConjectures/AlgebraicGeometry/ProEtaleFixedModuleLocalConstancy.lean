/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Local constancy with fixed module coefficients on the pro-etale site

Source: Bhatt--Scholze, Definition 7.3.1(1), with module coefficients;
Stacks Project, Tag 099Y (auxiliary; not a blueprint node).

This is the fixed-coefficient encoding used by the canonical comparison adjunction.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Local constancy of a fixed-coefficient module sheaf means a pro-etale covering of
`Y` on whose members its localized restriction is isomorphic to a constant module sheaf.
The constants are sheafifications of constant module presheaves, including their scalar
multiplication. The modules may vary and need not be finite. This is the encoding needed by the
module-valued comparison adjunction.
Source: Bhatt--Scholze, Definition 7.3.1(1), module version; Stacks Project, Tag 099Y
(auxiliary; not a blueprint node). -/
noncomputable def IsLocallyConstantProEtaleFixedModuleSheaf (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → Y.ProEt)
    (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 Y)),
    Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _ ∧
      ∀ i : I, ∃ M : ModuleCat.{u + 1} A,
        Nonempty (F.over (U i) ≅
          (constantSheaf ((ProEt.topology Y).over (U i)) (ModuleCat.{u + 1} A)).obj M)

end AlgebraicGeometry.Scheme
