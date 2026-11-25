/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatSingleOpenNoetherianComparison
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.NoetherianProperBoundedCoherentImage
import WeilConjectures.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentLift
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.BoundedComplexTensorProperSupportBound
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectTensorBoundedCoherent
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # Pseudo-coherence of open restrictions of a proper relatively flat direct image

## References

* Stacks Project, Tag 0A1H, Noetherian approximation paragraph
* Stacks Project, Tag 0A1H, approximation paragraph, with E=O_X and G=F[0]
* Tags 02O5, 08E7, 08E5
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The open restriction of the direct image is pseudo-coherent, without a Tor bound. -/
theorem properFlat_single_open_isPseudoCoherent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    U.toScheme.IsPseudoCoherent ((schemeOpenRestriction S U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) := by
  intro x
  obtain ⟨V, hx, T, Y, W, hT, hW, hnoeth, dT, dW, dY, dO,
    p, hproper, A, hAb, hAc, g, L, ⟨eL⟩, hL, hcompare⟩ :=
    properFlat_single_open_noetherian_comparison f F hF U x
  let := hT
  let := hnoeth
  let := dT
  let := dW
  let := dY
  let := dO
  let := hproper
  let := hL
  obtain ⟨hb, hc⟩ := Scheme.noetherian_proper_directImage_bounded_coherent p A hAb hAc
  have hpc := Scheme.isPseudoCoherent_of_bounded_coherent W.toScheme
    ((schemeDerivedDirectImage p).obj A) hb hc
  obtain ⟨P, hPb, hPf, hPe⟩ := Scheme.exists_boundedAbove_finiteFree_lift T W hW
    ((schemeDerivedDirectImage p).obj A) hpc
  let K := (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  refine ⟨V, hx, K, ?_, ?_, hcompare P hPb hPf hPe⟩
  · obtain ⟨N, hN⟩ := hPb
    exact ⟨N, fun i hi ↦ L.map_isZero (hN i hi)⟩
  · intro i
    obtain ⟨r, ⟨e⟩⟩ := hPf i
    let q := g ≫ W.ι
    obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction q
    let : (Scheme.Modules.tensorPullback q).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    have : IsIso (Scheme.Modules.tensorPullbackObjUnitToUnit q) :=
      (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso q).1
    let eunit := asIso (Scheme.Modules.tensorPullbackObjUnitToUnit q)
    let eV := Scheme.Modules.overEquiv V
    let eFree := (SheafOfModules.mapFreeIso (Scheme.Modules.tensorPullback q)
      (ULift.{u} (Fin r)) eunit.symm).symm
    let eOver := (SheafOfModules.mapFreeIso eV.inverse (ULift.{u} (Fin r))
      (V.sheafOfModulesEquivOverInverseUnit
        (moduleRings U.toScheme.toRingedSpace)).symm).symm
    exact ⟨r, ⟨L.mapIso e ≪≫ eL.app _ ≪≫ eV.inverse.mapIso eFree ≪≫ eOver⟩⟩

end AlgebraicGeometry
