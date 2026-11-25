/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Localization.Away.Basic

import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentPrincipalModel
import WeilConjectures.AlgebraicGeometry.SchemeIsoNestedOpenFiniteFreeModel

/-! # Pointwise pseudo-coherent localization on an affine open

Source: Stacks Project, Tags 08EE and 08E7
(blueprint: lem-sc-affine-open-pseudo-coherent-localization-point).
-/

@[expose] public section

set_option autoImplicit false

universe u w wL

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

local instance instAdditiveModuleCatExtendScalars_affineOpenPseudoCoherentLocalizationPoint
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
/-- Pseudo-coherence of a fixed associated-sheaf complex on an open supplies a
pseudo-coherent localization near each point of that open.
Source: Stacks Project, Tags 08EE and 08E7, local-model step
(blueprint: lem-sc-affine-open-pseudo-coherent-localization-point).

Proof: At x use the finite-free neighbourhood model in the definition of
pseudo-coherence on U. Its image in X is an open neighbourhood W contained in U.
The affine principal-open basis gives f with x in D(f) contained in W.
Transport X and W along X.isoSpec, and transport the finite-free model along
this isomorphism and the equivalence of the open scheme with its localized site.
Exact restriction preserves the upper bound and every finite free term: its
comparison with the unit sheaf and preservation of coproducts give the same ranks.
The derived restriction composition comparison transports the model isomorphism.
Use hT to identify the transported complex with termwise tilde of M on Spec A.
Apply affine_pseudoCoherent_principal_model to W and D(f). This gives the
pseudo-coherence of Q(M_f). No compactness or global finite cover is used.
For empty U there is no point to consider; empty principal opens cause no issue,
since their rings are zero and the principal-model theorem includes the zero ring.
-/
theorem affine_open_pseudoCoherent_localization_point
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [∀ f : X.presheaf.obj (.op ⊤), HasDerivedCategory.{wL}
      (ModuleCat.{u} (Localization.Away f))]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ)
    (hM : IsPseudoCoherent U.toScheme
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))))
    (x : X) (hx : x ∈ U) :
    ∃ f : X.presheaf.obj (.op ⊤), x ∈ X.basicOpen f ∧ X.basicOpen f ≤ U ∧
      DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars
            (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away f)))
          (ComplexShape.up ℤ)).obj M)) := by
  classical
  let A := X.presheaf.obj (.op ⊤)
  let Y := Spec A
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let := fun W : Y.Opens ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))
  have : (tilde.functor A).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let C := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  let D := ((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  obtain ⟨t⟩ := hT
  have hC : Nonempty (C ≅
      ((Modules.restrictFunctor X.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj D) :=
    ⟨HomologicalComplex.Hom.isoOfComponents (fun i ↦ t.app (M.X i))
      (fun i j _ ↦ (t.hom.naturality (M.d i j)).symm)⟩
  obtain ⟨V, hxV, P, hb, hfree, hiso⟩ := hM ⟨x, hx⟩
  obtain ⟨W, hW, P', hb', hfree', hiso'⟩ :=
    exists_scheme_iso_nested_open_finite_free_model X.isoSpec U C D hC V P hb hfree hiso
  have hxW : X.isoSpec.hom x ∈ W := (hW x).mpr ⟨hx, hxV⟩
  obtain ⟨B, ⟨f, rfl⟩, hxf, hfW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp W.isOpen
      (X.isoSpec.hom x) hxW
  have hbasic (y : X) : y ∈ X.basicOpen f ↔
      X.isoSpec.hom y ∈ PrimeSpectrum.basicOpen f := by
    change y ∈ X.basicOpen f ↔ y ∈ X.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f
    rw [X.map_PrimeSpectrum_basicOpen_of_affine]
  refine ⟨f, (hbasic x).mpr hxf, ?_, ?_⟩
  · intro y hy
    obtain ⟨hyU, _⟩ := (hW y).mp (hfW ((hbasic y).mp hy))
    exact hyU
  · exact affine_pseudoCoherent_principal_model A M f W hfW P' hb' hfree' hiso'

end AlgebraicGeometry.Scheme
