/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Standard.StandardFlatSingleBaseChangeMono
import WeilConjectures.AlgebraicGeometry.Standard.StandardFlatSingleBaseChangeEpi

/-! # Standard flat single base change for the canonical pullback

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor.
(blueprint: lem-pc-standard-flat-single-base-change).

The standard-localization degree-zero flat comparison is the intermediate result
needed by the localized cartesian comparison. Its proof follows the stalkwise
K-flat comparison and qcqs single-complex induction described in the DAG node.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Standard-localization degree-zero flat base change.

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor, specialized to
E = O_Y[0] and G = M[0].
(blueprint: lem-pc-standard-flat-single-base-change).

Proof: Construct the canonical forward comparison by composing the derived
base-change mate with direct image of the universal pullback counit on M[0],
then identify termwise pullback of a single complex with the single on q^*M.
The two cohomological comparison lemmas supply respectively monicity and
epicity of its map in every integer degree. In the abelian category of module
sheaves, a map which is both mono and epi is an isomorphism. The derived
cohomology functors jointly reflect isomorphisms, so the constructed comparison
is an isomorphism. Invert it to obtain the requested orientation and package it
in Nonempty. The cohomological lemmas use relative flatness over B, affine
scalar-extension calculations and qcqs source-open Mayer--Vietoris induction;
no flatness over O_Y or flatness of g is used. Zero modules, empty schemes,
and every integer cohomological degree are included. -/
theorem standard_flat_single_baseChange
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    Nonempty ((schemeDerivedDirectImage (pullback.snd p g)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M)) ≅
      (derivedPullback g).obj ((schemeDerivedDirectImage p).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M))) := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  have h : IsIso (standardSingleBaseChangeMap p M g) := by
    apply (DerivedCategory.isIso_iff
      (SheafOfModules.{u} (moduleRings A.toRingedSpace)) _).mpr
    intro n
    have := standard_flat_single_baseChange_homology_mono p M hM g n
    have := standard_flat_single_baseChange_homology_epi p M hM g n
    exact isIso_of_mono_of_epi _
  exact ⟨(asIso (standardSingleBaseChangeMap p M g)).symm⟩

end AlgebraicGeometry
