/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesPrimeCoefficients
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesPrimeCharP
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothConnectedFibreDimensionLoci
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ConnectedFibresConstantDegreeZero
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperBaseChangeHomology
import WeilConjectures.ConstructibleSheaf.FiniteDerived
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.OpenCover
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Prime coefficients in proper smooth curve families in every characteristic

This is the prime-coefficient part of Stacks Project, Tag 0GKW.  It is separated
from the finite-module dévissage so that the characteristic-p argument is explicit.
(blueprint: lem-fd-proper-smooth-curves-prime-all-char)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Compare the bounded below and the unbounded models of the same higher direct image.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[irreducible]
private noncomputable def constantHigherDirectImagePlusIso
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
private theorem exists_smoothOfRelativeDimension_of_connectedSpace
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

-- The geometric fibres of a smooth geometrically connected morphism have the dimension of
-- the residue-field fibres.
private theorem topologicalKrullDim_geometricFiber_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] (s : S) :
    topologicalKrullDim
      ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) = topologicalKrullDim (f.fiber s) := by
  have : Smooth (f.fiberToSpecResidueField s) :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_of_connectedSpace
    (f.fiberToSpecResidueField s)
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

-- Base change of a smooth morphism with geometrically connected fibres preserves the
-- dimension of the fibres.
private theorem topologicalKrullDim_fiber_of_isPullback_of_smooth
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Smooth f] [GeometricallyConnected f] (y : Y) :
    topologicalKrullDim (snd.fiber y) = topologicalKrullDim (f.fiber (g y)) := by
  have : Smooth (f.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have : ConnectedSpace (f.fiber (g y)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback _ _)
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_of_connectedSpace
    (f.fiberToSpecResidueField (g y))
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  have : GeometricallyConnected snd :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h ‹_›
  have : ConnectedSpace (snd.fiber y) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _
      (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension n (snd.fiberToSpecResidueField y) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
      (isPullback_fiberToSpecResidueField_of_isPullback h y) hn
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (f.fiberToSpecResidueField (g y)) n,
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (snd.fiberToSpecResidueField y) n]

-- The unbounded higher direct images of a constant sheaf along a finite flat morphism with
-- geometrically connected fibres are constructible.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem finite_constant_homology_constructible
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
              ((constantSheaf X.smallEtaleTopology _).obj M)))) :=
      higherDirectImage_zero_constant_constructible f M
    exact Scheme.IsConstructibleSheaf.of_iso (constantHigherDirectImagePlusIso f M 0)
  · exact Scheme.IsConstructibleSheaf.of_isZero
      (isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite f _ q hq)

-- Constructibility of the unbounded higher direct images of a constant sheaf follows from
-- constructibility of its bounded below higher direct images in nonnegative degrees.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem constant_homology_constructible_of_higherDirectImage
    {X S : Scheme.{u}} (f : X ⟶ S) (R : Type (u + 1)) [CommRing R]
    (M : ModuleCat.{u + 1} R)
    (h : ∀ n : ℕ, Scheme.IsConstructibleSheaf (higherDirectImage R f n
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))) (q : ℤ) :
    Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology _).obj M)))) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).obj
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} R) f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology _).obj M)))) := h n
    exact Scheme.IsConstructibleSheaf.of_iso (constantHigherDirectImagePlusIso f M n)
  · have hge := (lowerStar (ModuleCat.{u + 1} R) f).isGE_rightDerivedFunctor_obj_singleFunctor
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    exact Scheme.IsConstructibleSheaf.of_isZero
      ((DerivedCategory.isGE_iff _ 0).mp hge q (by omega))

-- On a dimension-one family, split the base into the open locus where `p` is invertible and
-- the reduced closed locus where `p` vanishes, and use proper base change on both.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem dimension_one_prime_homology_constructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (p : ℕ) [Fact p.Prime] (q : ℤ) :
    Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology _).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))))))) := by
  let R := ULift.{u + 1} (ZMod p)
  let M := ModuleCat.of R R
  let V := S.basicOpen (p : Γ(S, ⊤))
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(V : Set S)ᶜ, V.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds S)
  let i := I.subschemeι
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    simp [i, I, Scheme.IdealSheafData.range_subschemeι]
  rw [Scheme.isConstructibleSheaf_iff_upperStar V.ι i hij]
  constructor
  · let g := Limits.pullback.snd f V.ι
    have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
    have : TopologicalSpace.NoetherianSpace V.toScheme :=
      V.ι.isOpenEmbedding.isInducing.noetherianSpace
    have hunit (s : V.toScheme) : IsUnit (p : V.toScheme.presheaf.stalk s) := by
      have hs : V.ι s ∈ V := by simp
      have := (S.mem_basicOpen_top _ _).mp hs
      rw [map_natCast] at this
      simpa using this.map (V.ι.stalkMap s).hom
    have hdimV (s : V.toScheme) : topologicalKrullDim (g.fiber s) = 1 :=
      (topologicalKrullDim_fiber_of_isPullback_of_smooth
        (IsPullback.of_hasPullback f V.ι) s).trans (hdim _)
    have := constant_homology_constructible_of_higherDirectImage g R M (fun n ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (properSmoothCurves_prime_higherDirectImage_constructible g hdimV p hunit n)) q
    exact Scheme.IsConstructibleSheaf.of_iso
      (upperStarHomologyRightDerivedLowerStarConstantSheafIso
        (IsPullback.of_hasPullback f V.ι) M q).symm
  · let g := Limits.pullback.snd f i
    have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
    have : IsNoetherian I.subscheme := ⟨⟩
    have hp : (p : Γ(I.subscheme, ⊤)) = 0 := by
      apply (basicOpen_eq_bot_iff _).mp
      rw [← map_natCast i.appTop.hom p, ← Scheme.preimage_basicOpen_top]
      refine eq_bot_iff.mpr fun z hz ↦ ?_
      have hz' : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
      rw [hij] at hz'
      exact (hz' ⟨⟨i.base z, hz⟩, rfl⟩).elim
    have hdimZ (s : I.subscheme) : topologicalKrullDim (g.fiber s) = 1 :=
      (topologicalKrullDim_fiber_of_isPullback_of_smooth
        (IsPullback.of_hasPullback f i) s).trans (hdim _)
    have := constant_homology_constructible_of_higherDirectImage g R M (fun n ↦
      properSmoothCurves_charP_higherDirectImage_constructible g hdimZ p hp n) q
    exact Scheme.IsConstructibleSheaf.of_iso
      (upperStarHomologyRightDerivedLowerStarConstantSheafIso
        (IsPullback.of_hasPullback f i) M q).symm

/-- Prime coefficients for proper smooth geometrically connected relative curves.

Source: Stacks Project, more-etale.tex, Tags 0GKV and 0GKW.
(blueprint: lem-fd-proper-smooth-curves-prime-all-char)

Proof: use the clopen dimension-zero/dimension-one decomposition.  On the
dimension-zero locus, proper plus quasi-finite is finite and finite direct image
is exact.  On the dimension-one locus split the base into the open where `p` is
invertible and the closed characteristic-`p` locus.  The open part is the
prime-coefficient theorem `properSmoothCurves_prime_higherDirectImage_constructible`.
On the closed part, proper base change, Artin--Schreier, and the Frobenius-fixed
sections sequence reduce the assertion to the kernel of Frobenius minus identity
on the finite locally free degree-one structure-cohomology bundle.  The
Frobenius-linear vector-bundle constructibility theorem, finite geometric stalks,
and the module/abelian comparison finish that branch.  The two restrictions are
identified by exact pullback and proper base change, and the finite stratifications
are glued.
-/
theorem properSmoothCurves_prime_higherDirectImage_constructible_all_char
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (p : ℕ) [Fact p.Prime] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))) q).obj
        ((rightDerivedLowerStarPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))) 0).obj
            ((constantSheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod p))
                (ULift.{u + 1} (ZMod p))))))) := by
  classical
  have : IsNoetherian S := ⟨⟩
  let R := ULift.{u + 1} (ZMod p)
  let M := ModuleCat.of R R
  let F := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  let G := (DerivedCategory.homologyFunctor _ q).obj
    ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F))
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  suffices Scheme.IsConstructibleSheaf G from
    Scheme.IsConstructibleSheaf.of_iso (constantHigherDirectImagePlusIso f M q).symm
  obtain ⟨U, hU, -, -, hcover, -, hzero⟩ :=
    proper_smooth_connected_fibre_dimension_loci f 1
      (fun s ↦ GeometricallyConnected.geometrically_connectedSpace _ _ _
        (IsPullback.of_hasPullback _ _))
      (fun s ↦ (topologicalKrullDim_geometricFiber_eq f s).trans_le (h_dim s))
  apply Scheme.IsConstructibleSheaf.of_iSup_eq_top U hcover G
  intro i
  have : IsLocallyNoetherian (U i).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (U i).ι
  have : TopologicalSpace.NoetherianSpace (U i).toScheme :=
    (U i).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : IsNoetherian (U i).toScheme := ⟨⟩
  let g := Limits.pullback.snd f (U i).ι
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} R) g).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Limits.pullback f (U i).ι).smallEtaleTopology _).obj M)))) := by
    fin_cases i
    · have : LocallyQuasiFinite g := by
        apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
        intro x
        apply isDiscrete_iff_discreteTopology.mpr
        apply discreteTopology_iff_isOpen_singleton.mpr
        rintro ⟨y, hy⟩
        obtain rfl : g y = x := hy
        have hopen : IsOpen ({g.asFiber y} : Set (g.fiber (g y))) := hzero.2.2 y
        rw [← (g.fiberHomeo (g y)).isOpen_image] at hopen
        simpa only [Set.image_singleton, Scheme.Hom.asFiber,
          Homeomorph.apply_symm_apply] using hopen
      have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
      exact finite_constant_homology_constructible g R M q
    · apply dimension_one_prime_homology_constructible g _ p q
      intro s
      have hi : topologicalKrullDim (f.fiber ((U 1).ι s)) = 1 := by
        rw [← topologicalKrullDim_geometricFiber_eq f ((U 1).ι s)]
        have hs : (U 1).ι s ∈ (U 1 : Set S) := s.property
        rw [hU 1] at hs
        exact hs
      exact (topologicalKrullDim_fiber_of_isPullback
        (IsPullback.of_hasPullback f (U 1).ι) s).trans hi
  exact Scheme.IsConstructibleSheaf.of_iso
    (upperStarHomologyRightDerivedLowerStarConstantSheafIso
      (IsPullback.of_hasPullback f (U i).ι) M q).symm

end AlgebraicGeometry.Etale
