/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.TruncatedHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine evaluation of coproducts of lower-truncated higher images

Source: Stacks Project, Tags 08D5 and 015J, with Schemes, Tag 01I7
(blueprint: lem-pc-truncated-higher-images-affine-coproduct).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sheaf coproduct of lower-truncated higher images is a coproduct on affine sections.
This assertion concerns only the family of higher-image sheaves; no ambient derived
coproduct or its higher direct image occurs in its statement.
Source: Stacks Project, Tag 08D5, bounded-below paragraph, and Tag 015J; Tag 01I7
(blueprint: lem-pc-truncated-higher-images-affine-coproduct).

Proof.
1. Canonical lower truncation preserves quasi-coherent cohomology: the cohomology is
   unchanged in degrees at least a and zero below a. It has common lower bound a.
2. For each i, apply bounded-below truncation hypercohomology for direct image. Its
   second page is R^p f_* H^r. On an affine target open the preimage is qcqs. Ordinary
   higher images of quasi-coherent modules are quasi-coherent: affine acyclicity and
   localization of sections give localization of cohomology in the affine case;
   Mayer--Vietoris on a finite affine cover, with quasi-compact overlaps supplied by
   quasi-separatedness, gives it for the preimage. These comparisons commute with
   principal restriction. The higher-image presheaf description therefore gives
   the affine localization criterion for quasi-coherence of the second-page sheaves.
3. Closure under kernels and cokernels/images gives quasi-coherence of all later
   pages. In total degree q the convergent filtration is finite, and its graded
   pieces are stable terms of these pages. Descending extension induction from its
   zero last step makes the abutment quasi-coherent. Below the bound a it is zero.
4. Arbitrary sheaf coproducts of quasi-coherent modules are quasi-coherent. Apply
   affine evaluation of quasi-coherent colimits to their canonical coproduct cocone.
   This gives the displayed module colimit, including an empty index type and the
   empty affine open. No claim that arbitrary module-sheaf coproducts are sectionwise
   is needed.
-/
theorem truncated_higherImages_affine_coproduct
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (a q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    Nonempty (IsColimit
      ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).mapCocone
        (Cofan.mk
          (∐ (fun i ↦ (schemeHigherDirectImage f q).obj
            ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)))
          (Sigma.ι (fun i ↦ (schemeHigherDirectImage f q).obj
            ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)))))) := by
  let M : I → Y.Modules := fun i ↦ (schemeHigherDirectImage f q).obj
    ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)
  have hM : ∀ i, (M i).IsQuasicoherent := fun i ↦
    truncated_higherImage_isQuasicoherent f (E i) a q
  let : ∀ i, (M i).IsQuasicoherent := hM
  have hsum : (∐ M).IsQuasicoherent := Scheme.Modules.isQuasicoherent_sigma M
  exact Scheme.Modules.quasiCoherentModuleColimitEvaluation Y (Discrete I)
    (Discrete.functor M) (Cofan.mk (∐ M) (Sigma.ι M))
    (coproductIsCoproduct M) (fun i ↦ hM i.as) hsum U hU

end AlgebraicGeometry
