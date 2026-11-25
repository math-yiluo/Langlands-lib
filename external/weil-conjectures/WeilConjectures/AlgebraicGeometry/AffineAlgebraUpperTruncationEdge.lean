/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing


public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.LeftExactUpperTruncationComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.DerivedLowerTruncationCycleFormula
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # The canonical affine derived edge after upper truncation

Source: Stacks Project, Tags 0AVW and 08D4, with bound N = 1.
(blueprint: lem-sc-affine-algebra-upper-truncation-edge).
-/

@[expose] public section
set_option autoImplicit false

universe v wX wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Direct image preserves finite limits, since underlying sections are evaluated on
inverse-image opens. Source: Stacks Project, Tag 079V.
(blueprint: lem-sc-affine-algebra-upper-truncation-edge). -/
theorem affineAlgebraDirectImage_preservesFiniteLimits
    {X Y : Scheme.{v}} (f : X ⟶ Y) :
    PreservesFiniteLimits (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let U := SheafOfModules.forget (moduleRings (directImageAlgebraSpace f))
  let V := PresheafOfModules.toPresheaf (moduleRings (directImageAlgebraSpace f)).obj
  have : PreservesFiniteLimits (F ⋙ U ⋙ V) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map f.base).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F (U ⋙ V)

attribute [instance] affineAlgebraDirectImage_preservesFiniteLimits

private theorem restriction_properties {Z : TopCat.{v}}
    (O A : Z.Sheaf RingCat.{v}) (φ : O ⟶ A) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{v} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{v} φ) ∧
        (SheafOfModules.restrictScalars.{v} φ).ReflectsIsomorphisms := by
  let T := SheafOfModules.restrictScalars.{v} φ
  have : PreservesFiniteLimits (T ⋙ SheafOfModules.toSheaf O) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf A)
    infer_instance
  have hlim : PreservesFiniteLimits T :=
    preservesFiniteLimits_of_reflects_of_preserves T (SheafOfModules.toSheaf O)
  have : PreservesFiniteColimits (T ⋙ SheafOfModules.toSheaf O) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf A)
    infer_instance
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf O) :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have hcolim : PreservesFiniteColimits T :=
    preservesFiniteColimits_of_reflects_of_preserves T (SheafOfModules.toSheaf O)
  have : (T ⋙ SheafOfModules.toSheaf O).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf A).ReflectsIsomorphisms
  exact ⟨hlim, hcolim, reflectsIsomorphisms_of_comp T (SheafOfModules.toSheaf O)⟩

private theorem affineAlgebra_lowerTruncation_isIso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).map
        ((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).rightDerivedFunctor.map
          ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I)))) := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))
  let B := SheafOfModules.{v} (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard B
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let G := F.rightDerivedFunctor
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  obtain ⟨hlim, hcolim, hreflect⟩ := restriction_properties
    (moduleRings Y.toRingedSpace) (moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  have : PreservesFiniteLimits T := hlim
  have : PreservesFiniteColimits T := hcolim
  have : T.ReflectsIsomorphisms := hreflect
  have underived : F ⋙ T ≅ RingedSpace.moduleDirectImage f.toLRSHom.toShHom :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro M N g
      ext U x
      rfl)
  let comparison : G ⋙ T.mapDerivedCategory ≅ schemeDerivedDirectImage f :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).symm ≪≫
      Functor.rightDerivedFunctorNatIso underived
  have : IsGrothendieckAbelian.{v} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  have hacyc : ∀ (M : C), M.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
      Limits.IsZero ((schemeModuleHigherDirectImage f p).obj M) := by
    intro M hM p hp
    have := hM
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) := ⟨p.toNat, by omega⟩
    have hm : 0 < m := by omega
    have hz := Scheme.Modules.isZero_higherDirectImage_of_isAffineHom f M hm
    exact hz.of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) M m)
  let E := DerivedCategory.Q.obj I
  have hE : schemeDerivedQCohProperty X E := by
    intro i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors C i).app I).symm (hI i)
  let t := DerivedCategory.TStructure.t (C := C)
  let E' := (t.truncGE n).obj E
  let Q := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
  have hzero : Limits.IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
      PEmpty.{v + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext j
    exact PEmpty.elim j
  have : Q.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{v + 1}⟩⟩
  have hE' : schemeDerivedQCohProperty X E' :=
    DerivedCategory.homologyProperty_truncGE hE n
  let u := (t.truncGEπ n).app E
  let u' : (⟨E, hE⟩ : schemeDerivedQCohCategory X) ⟶ ⟨E', hE'⟩ :=
    (schemeDerivedQCohProperty X).homMk u
  let H := DerivedCategory.homologyFunctor D n
  -- The natural affine comparison makes the truncation projection invertible over O_Y.
  obtain ⟨e⟩ := qcoh_acyclic_derived_pushforward_cohomology f hacyc n
  have : IsIso ((DerivedCategory.homologyFunctor C n).map u) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E n n le_rfl
  have hpush : IsIso (((schemeDerivedQCohProperty X).ι ⋙
      DerivedCategory.homologyFunctor C n ⋙
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map u') := by
    change IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map
      ((DerivedCategory.homologyFunctor C n).map u))
    infer_instance
  have hscheme := (NatIso.isIso_map_iff e u').2 hpush
  change IsIso ((DerivedCategory.homologyFunctor B n).map
    ((schemeDerivedDirectImage f).map u)) at hscheme
  let c : G ⋙ H ⋙ T ≅ schemeDerivedDirectImage f ⋙
      DerivedCategory.homologyFunctor B n :=
    Functor.isoWhiskerLeft G (T.mapDerivedCategoryHomologyFunctorIso n) ≪≫
      Functor.isoWhiskerRight comparison (DerivedCategory.homologyFunctor B n)
  have hT := (NatIso.isIso_map_iff c u).2 hscheme
  change IsIso (T.map (H.map (G.map u))) at hT
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ T hT _

set_option backward.isDefEq.respectTransparency false in
private theorem factors_normalization
    {C : Type (v + 1)} [Category.{v} C] [Abelian C]
    {D : Type (v + 1)} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{wY} D]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    let H := DerivedCategory.homologyFunctor D n
    ((DerivedCategory.homologyFunctorFactors D n).app J).inv ≫
      H.map ((DerivedCategory.quotientCompQhIso D).inv.app J) =
    ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).inv ≫
      ((DerivedCategory.homologyFunctorFactorsh D n).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj J)).inv := by
  dsimp only
  simp only [Iso.app_inv]
  rw [DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj]
  simp only [Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem unit_naturality
    {C : Type (v + 1)} [Category.{v} C] [Abelian C]
    {D : Type (v + 1)} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{wX} C] [HasDerivedCategory.{wY} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    (β : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor)
    {A I : CochainComplex C ℤ} (i : A ⟶ I) (n : ℤ)
    [IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map i) n)] :
    let M := F.mapHomologicalComplex (.up ℤ)
    let H := DerivedCategory.homologyFunctor D n
    inv (HomologicalComplex.homologyMap (M.map i) n) ≫
        ((DerivedCategory.homologyFunctorFactors D n).app (M.obj A)).inv ≫
        H.map (β.app A) ≫ H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map i)) =
      ((DerivedCategory.homologyFunctorFactors D n).app (M.obj I)).inv ≫
        H.map (β.app I) := by
  dsimp only
  simp only [Iso.app_inv]
  have hβ := congrArg (DerivedCategory.homologyFunctor D n).map (β.naturality i)
  simp only [Functor.comp_map, Functor.map_comp] at hβ
  rw [← hβ]
  have hF := (DerivedCategory.homologyFunctorFactors D n).inv.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map i)
  dsimp only [Functor.comp_map] at hF
  rw [← reassoc_of% hF]
  change inv (HomologicalComplex.homologyMap
    ((F.mapHomologicalComplex (.up ℤ)).map i) n) ≫
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map i) n ≫ _ = _
  simp only [IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem upperTruncation_edge_of_lowerIso
    {C : Type (v + 1)} [Category.{v} C] [Abelian C]
    {D : Type (v + 1)} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{wX} C] [HasDerivedCategory.{wY} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ)
    (hLower : IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))))) :
    ∃ e : (DerivedCategory.homologyFunctor D n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (I.truncLE n))) ≅
        F.obj (I.sc n).homologyData.left.H,
      cokernel.π (F.map (I.sc n).homologyData.left.f') ≫
          F.upperTruncationBoundaryComparison I n ≫ e.hom =
        F.map (I.sc n).homologyData.left.π := by
  let H := DerivedCategory.homologyFunctor D n
  let i := I.ιTruncLE n
  let p := (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I)
  have hs : IsIso (H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map i))) :=
    F.upperTruncation_derived_comparison I n
  have hp : IsIso (H.map (F.rightDerivedFunctor.map p)) :=
    hLower
  have hr : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map i) n) :=
    F.upperTruncation_raw_comparison I n
  obtain ⟨b, hb⟩ := derived_lower_truncation_cycle_formula F I n
  refine ⟨asIso (H.map (F.rightDerivedFunctor.map (DerivedCategory.Q.map i))) ≪≫
    asIso (H.map (F.rightDerivedFunctor.map p)) ≪≫ b, ?_⟩
  simp only [Iso.trans_hom, asIso_hom]
  dsimp only [Functor.upperTruncationBoundaryComparison]
  simp only [Category.assoc]
  rw [reassoc_of% (unit_naturality F F.complexDerivedUnit i n)]
  have hc : cokernel.π (F.map (I.sc n).homologyData.left.f') ≫
      (F.mappedCyclesHomologyData I n).homologyIso.inv =
      (((F.mapHomologicalComplex (.up ℤ)).obj I).sc n).liftCycles
        (F.map (I.sc n).homologyData.left.i) (by
          change F.map (I.sc n).homologyData.left.i ≫ F.map (I.sc n).g = 0
          rw [← F.map_comp, (I.sc n).homologyData.left.wi, F.map_zero]) ≫
        (((F.mapHomologicalComplex (.up ℤ)).obj I).sc n).homologyπ := by
    change (F.mappedCyclesHomologyData I n).π ≫ _ = _
    rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
    apply congrArg (fun z ↦ z ≫
      (((F.mapHomologicalComplex (.up ℤ)).obj I).sc n).homologyπ)
    apply (cancel_mono (((F.mapHomologicalComplex (.up ℤ)).obj I).sc n).iCycles).mp
    erw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ShortComplex.liftCycles_i]
    rfl
  rw [← Category.assoc, hc]
  dsimp only [Functor.complexDerivedUnit]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [reassoc_of% (factors_normalization F I n)]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] using hb


/-- The derived upper-truncation edge is an isomorphism and sends the canonical image
of a cycle to its original homology-sheaf class. K-injectivity is not assumed here.
Source: Stacks Project, Tag 0AVW, cohomology display and its omitted detail;
Tag 08D4 (2) and (3), N = 1, and Tag 05TC.
(blueprint: lem-sc-affine-algebra-upper-truncation-edge).

Proof: Put A = tau<=n I and B = tau>=n A. The lower tail tau<=n-1 I has
quasi-coherent cohomology. On inverse images of affine opens, affine vanishing and
the bound of Tag 08D4 with N=1 give zero derived sections of this tail in degrees
n and n+1. Its truncation triangle therefore makes H^n(RGamma(A)) -> H^n(RGamma(B))
invertible. B is canonically H^n(I) placed in degree n; bottom derived cohomology
is ordinary sections, by left exactness and the degree-zero derived comparison.
The resulting restriction-compatible, scalar-linear edge maps glue to the displayed
isomorphism over f_*O_X. For its formula use the natural comparison from raw sections
to derived sections in the square A -> B. In degree n this map is the quotient of
cycles by boundaries. The raw truncation inclusion A -> I is invertible on degree-n
homology under the left exact direct-image functor. Its inverse, the canonical
cokernel-to-homology isomorphism, and the comparison unit are exactly the factors in
upperTruncationBoundaryComparison. Thus the naturality square gives the asserted
identity after the cokernel projection. No K-injectivity or boundedness of I is used.
Empty affine opens, the zero complex, and every integer degree are included. -/
theorem affine_algebra_upper_truncation_edge
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    [EnoughInjectives (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
    ∃ e : (DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (I.truncLE n))) ≅
        F.obj (I.sc n).homologyData.left.H,
      cokernel.π (F.map (I.sc n).homologyData.left.f') ≫
          F.upperTruncationBoundaryComparison I n ≫ e.hom =
        F.map (I.sc n).homologyData.left.π := by
  dsimp only
  exact upperTruncation_edge_of_lowerIso
    (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) I n
    (affineAlgebra_lowerTruncation_isIso f I hI n)

end AlgebraicGeometry
