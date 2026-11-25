/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import Mathlib.Data.Set.PowersetCard

import WeilConjectures.AlgebraicGeometry.KoszulExtCoefficientAffineModel
import WeilConjectures.AlgebraicGeometry.KoszulQuotientHomologyFrame

/-! # Affine zero-differential self Ext calculation -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Self Ext before pullback is a finite coproduct of the quotient structure module.
Source: Stacks Project, Tag 0BQY, Lemma 48.15.4.
(blueprint: lem-u1-koszul-self-ext-quotient-frame).

Proof: Resolve the quotient A/I by the augmented Koszul complex of f. Its terms
are finite free on increasing subsets. Sheafify the resolution on U and use the
bounded-above finite-free internal Hom comparison. Hom into A/I has zero
differential because every f_j vanishes in A/I. Thus degree n cohomology is a
copy of A/I for each n-element subset. The wedge coordinate maps commute with
localization and give the asserted isomorphism on the over-U site. Compare
arbitrary derived universes by the same K-injective model. Empty charts, m=0,
and n>m use respectively zero rings, the empty wedge, and an empty coproduct. -/
theorem koszul_self_ext_quotient_frame
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (U : Y.affineOpens) (n : ℕ)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    Nonempty (G.over U.1 ≅
      (∐ fun _ : ULift.{u} (Set.powersetCard (Fin m) n) ↦ B).over U.1) := by
  classical
  dsimp only
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let a : SheafOfModules.unit Y.ringCatSheaf ⟶ B :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom
  obtain ⟨_, eG, _⟩ := koszulExtCoefficient_affine_model i m n U f hf hreg a rfl
  obtain ⟨eQ⟩ := koszul_quotient_homology_frame i U n m f hf
  let E := Scheme.Modules.overEquiv U.1
  let eR := Scheme.Modules.overFunctorEquiv U.1
  exact ⟨E.functor.preimageIso
    (eR.app _ ≪≫ eG ≪≫ eQ ≪≫ (eR.app _).symm)⟩

end AlgebraicGeometry
