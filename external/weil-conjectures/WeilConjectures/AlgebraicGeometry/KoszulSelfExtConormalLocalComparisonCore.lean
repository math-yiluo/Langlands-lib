/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtPullbackLocalFrame
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison

/-! # Local finite-free Koszul self-Ext identifications

Source: Stacks Project, Tag 0BQY and Tag 062I. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry


/-- Restrict a frame to the inverse image of its trivializing open. -/
private noncomputable def restrictLocalFrame
    {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) :
    (M.restrict V.ι).over (V.ι ⁻¹ᵁ U) ≅ SheafOfModules.free I :=
  (Scheme.Modules.overIsoFreeEquiv (M.restrict V.ι) (V.ι ⁻¹ᵁ U) I).symm
    (((Scheme.Modules.restrictFunctorComp _ _).app M).symm ≪≫
      Scheme.Modules.restrictCompIso M U.ι (V.ι ∣_ U) ((V.ι ⁻¹ᵁ U).ι ≫ V.ι)
        (morphismRestrict_ι V.ι U) ≪≫
      (Scheme.Modules.restrictFunctor _).mapIso
        (Scheme.Modules.overIsoFreeEquiv M U I e) ≪≫ Scheme.Modules.restrictFreeIso _ _)

/-- Every point has a local isomorphism from dual exterior conormal to self Ext.

Source: Stacks Project, Tag 0BQY (Hom of the Koszul resolution) and Tag 062I.
(blueprint: new-w4-koszul-self-ext-local-iso).

Proof: At z choose the supplied chart U and its regular generators. The existing
self-Ext pullback local frame identifies the target over i⁻¹U with the free sheaf
indexed by increasing n-element subsets. The regular conormal basis and affine
conormal frame identify i*ker(i) over i⁻¹U with the m-fold free sheaf. Apply the
exterior local-free comparison, then overHomObjIso and homObjFreeUnitIso to identify
its internal dual with the same subset-indexed free sheaf. Restrict both frames
along V.ι to V.ι⁻¹(i⁻¹U), using the over-to-restricted-site equivalence, composition
of open restriction, and restriction of free sheaves. Compose the restricted source
frame with the inverse restricted target frame. Membership is the original chart
membership. No generator comparison is required here. The already stated frame
lemmas include all derived universes, n=0, n>m, and empty charts. Empty V is vacuous.
-/
theorem koszulRegularImmersion_self_ext_conormal_local_iso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∀ z : V.toScheme, ∃ W : V.toScheme.Opens,
      z ∈ W ∧ Nonempty (F.over W ≅ T.over W) := by
  classical
  intro B S H G T F z
  obtain ⟨U, hzU, m, f, hf, hreg⟩ := hregular z.1 z.2
  let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let W := i ⁻¹ᵁ U.1
  obtain ⟨b, _⟩ := ExteriorAlgebra.exists_koszul_conormal_basis
    Γ(Y, U.1) (i.ker.ideal U) m f hreg hf
  obtain ⟨eC⟩ := (affine_conormal_frame i U m b).1
  obtain ⟨eE⟩ := (Scheme.Modules.exteriorSheaf_local_free_comparison Z C n W m eC).1
  let E := Scheme.Modules.exteriorPower C n
  let eF : (Scheme.Modules.dual E).over W ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin m) n)) :=
    SheafOfModules.overHomObjIso E (SheafOfModules.unit Z.ringCatSheaf) W ≪≫
      ((SheafOfModules.homFunctor (Z.sheaf.over W)).flip.obj
        (SheafOfModules.unit (Z.ringCatSheaf.over W))).mapIso eE.symm.op ≪≫
      SheafOfModules.homObjFreeUnitIso.{u} (R := Z.sheaf.over W) _
  obtain ⟨eT⟩ := koszulRegularImmersion_self_ext_pullback_local_frame i U n m f hf hreg
  refine ⟨V.ι ⁻¹ᵁ W, hzU, ⟨?_⟩⟩
  exact restrictLocalFrame (Scheme.Modules.dual E) W V eF ≪≫
    (restrictLocalFrame ((Scheme.Modules.tensorPullback i).obj G) W V eT).symm

end AlgebraicGeometry
