/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothConnectedFibreDimensionLoci
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesPrimeCoefficients
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ConnectedFibresConstantDegreeZero
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal
import WeilConjectures.ConstructibleSheaf.FiniteDerived
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructibility for proper smooth families of curves with finite coefficients

## References

* Tag 0GK3 for dimension zero, Tag 02G1 for the fibre-dimension decomposition
* Stacks Project, Tag 0GKW (dimension one), Tag 0GK3 (dimension zero), and Tag 02G1 (locally
  constant smooth fibre dimension)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Compare the two models of the same higher direct image.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[irreducible]
private noncomputable def constant_totalPlus_iso
    {X S : Scheme.{u}} (f : X ⟶ S) {R : Type (u + 1)} [CommRing R]
    (M : ModuleCat.{u + 1} R) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology _).obj M))) ≅
    (DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology _).obj M))) :=
  (DerivedCategory.homologyFunctor _ q).mapIso
    ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctorPlusCompatibility.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology _).obj M)))

-- A nonempty smooth connected scheme over a field has a single relative dimension.
private theorem fibre_relative_dimension
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [Smooth g] [ConnectedSpace Y] : ∃ n : ℕ, SmoothOfRelativeDimension n g := by
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := IsRegular.of_smooth g
  have := IsRegular.isIntegral Y
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U, V, -, -, hy, e, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE g y
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  have : SmoothOfRelativeDimension n (V.ι ≫ g) := by
    rw [← Scheme.Hom.resLE_comp_ι g e]
    have : SmoothOfRelativeDimension (n + 0) (g.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  refine ⟨n, (smoothOfRelativeDimension_iff_topologicalKrullDim_eq g n).mpr ?_⟩
  exact (topologicalKrullDim_opens_eq g V).symm.trans
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ g) n)

private theorem geometric_fibre_dimension_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] (s : S) :
    topologicalKrullDim
      ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) = topologicalKrullDim (f.fiber s) := by
  have : Smooth (f.fiberToSpecResidueField s) :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  obtain ⟨n, hn⟩ := fibre_relative_dimension (f.fiberToSpecResidueField s)
  have := hn
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (f.fiberToSpecResidueField s) n]
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))))
  have : ConnectedSpace ↥(Limits.pullback (f.fiberToSpecResidueField s) g) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback _ _)
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (Limits.pullbackLeftPullbackSndIso f
      (S.fromSpecResidueField s) g).hom.homeomorph.isHomeomorph]
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (Limits.pullback.snd (f.fiberToSpecResidueField s) g) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem dimension_one_finite_coefficients
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : ∀ (a : R) (s : S), IsUnit (addOrderOf a : S.presheaf.stalk s))
    (M : ModuleCat.{u + 1} R) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology _).obj M)))) := by
  have : NeZero (ringChar R) := ⟨CharP.char_ne_zero_of_finite R (ringChar R)⟩
  let φ : ULift.{u + 1} (ZMod (ringChar R)) →+* R :=
    (ZMod.castHom dvd_rfl R).comp ULift.ringEquiv.toRingHom
  have : Finite ((ModuleCat.restrictScalars.{u + 1} φ).obj M) := inferInstanceAs (Finite M)
  apply (isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff φ f M q).mp
  apply constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod f _ _ _ q
  intro p _ hp j
  have hunit (s : S) : IsUnit (p : S.presheaf.stalk s) := by
    let := CharP.addOrderOf_one R
    have h1 := hR 1 s
    rw [← ringChar.eq R (addOrderOf (1 : R))] at h1
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hp) h1
  let P := ULift.{u + 1} (ZMod p)
  let A := ModuleCat.{u + 1} P
  let F := (constantSheaf X.smallEtaleTopology A).obj (ModuleCat.of P P)
  by_cases hj : 0 ≤ j
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (properSmoothCurves_prime_higherDirectImage_constructible f hdim p hunit n)
    exact Scheme.IsConstructibleSheaf.of_iso
      (F := (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).obj
        ((rightDerivedLowerStarPlus A f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
      (constant_totalPlus_iso f (ModuleCat.of P P) (n : ℤ))
  · have hge := (lowerStar A f).isGE_rightDerivedFunctor_obj_singleFunctor F
    exact Scheme.IsConstructibleSheaf.of_isZero
      ((DerivedCategory.isGE_iff _ 0).mp hge j (by omega))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem finite_constant_total_constructible
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Flat f] [GeometricallyConnected f]
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (M : ModuleCat.{u + 1} R) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology _).obj M)))) := by
  by_cases hq : q = 0
  · subst q
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology _).obj M)))) := by
      exact higherDirectImage_zero_constant_constructible f M
    exact Scheme.IsConstructibleSheaf.of_iso (constant_totalPlus_iso f M 0)
  · exact Scheme.IsConstructibleSheaf.of_isZero
      (isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite f _ q hq)

/-- Higher direct images of a finite constant module in a proper smooth family with
nonempty geometrically connected fibres of dimension at most one are constructible,
when the additive orders of the coefficients are invertible on the base. `GeometricallyConnected`
includes nonempty fibres; dimension is measured on the residue-field fibres.
-/
theorem properSmoothCurves_finiteModule_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ (a : Λ) (s : S), IsUnit (addOrderOf a : S.presheaf.stalk s))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  classical
  have : IsNoetherian S := ⟨⟩
  let F := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let G := (DerivedCategory.homologyFunctor _ q).obj
    ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F))
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  suffices Scheme.IsConstructibleSheaf G from
    Scheme.IsConstructibleSheaf.of_iso (constant_totalPlus_iso f M q).symm
  obtain ⟨U, hU, -, -, hcover, -, hzero⟩ :=
    proper_smooth_connected_fibre_dimension_loci f 1
      (fun s ↦ GeometricallyConnected.geometrically_connectedSpace _ _ _
        (IsPullback.of_hasPullback _ _))
      (fun s ↦ (geometric_fibre_dimension_eq f s).trans_le (h_dim s))
  apply Scheme.IsConstructibleSheaf.of_iSup_eq_top U hcover G
  intro i
  have : IsLocallyNoetherian (U i).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (U i).ι
  have : TopologicalSpace.NoetherianSpace (U i).toScheme :=
    (U i).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace (U i).toScheme := inferInstance
  let g := Limits.pullback.snd f (U i).ι
  let H := (DerivedCategory.homologyFunctor _ q).obj
    ((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Limits.pullback f (U i).ι).smallEtaleTopology _).obj M)))
  have hΛi (a : Λ) (s : (U i).toScheme) :
      IsUnit (addOrderOf a : (U i).toScheme.presheaf.stalk s) := by
    simpa using (hΛ a ((U i).ι s)).map ((U i).ι.stalkMap s).hom
  have hH : Scheme.IsConstructibleSheaf H := by
    fin_cases i
    · have : LocallyQuasiFinite g := by
        apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
        intro x
        apply isDiscrete_iff_discreteTopology.mpr
        apply discreteTopology_iff_isOpen_singleton.mpr
        rintro ⟨y, hy⟩
        change g y = x at hy
        subst x
        have hopen : IsOpen ({g.asFiber y} : Set (g.fiber (g y))) := hzero.2.2 y
        rw [← (g.fiberHomeo (g y)).isOpen_image] at hopen
        simpa only [Set.image_singleton, Scheme.Hom.asFiber,
          Homeomorph.apply_symm_apply] using hopen
      have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
      exact finite_constant_total_constructible g Λ M q
    · apply dimension_one_finite_coefficients g _ Λ hΛi M q
      intro s
      have hi : topologicalKrullDim (f.fiber ((U 1).ι s)) = 1 := by
        rw [← geometric_fibre_dimension_eq f ((U 1).ι s)]
        have hs : (U 1).ι s ∈ (U 1 : Set S) := s.property
        rw [hU 1] at hs
        exact hs
      exact (topologicalKrullDim_fiber_of_isPullback
        (IsPullback.of_hasPullback f (U 1).ι) s).trans hi
  let e : (upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj G ≅ H :=
    upperStarHomologyRightDerivedLowerStarIso
      (IsPullback.of_hasPullback f (U i).ι) F q ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso
        ((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ)
              (Limits.pullback.fst f (U i).ι)).app M)))
  exact Scheme.IsConstructibleSheaf.of_iso e.symm

end AlgebraicGeometry.Etale
