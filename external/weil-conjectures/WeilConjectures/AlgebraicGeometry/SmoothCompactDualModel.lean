/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.FiniteLisseFieldDual
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionExchange
import WeilConjectures.AlgebraicGeometry.CompactModelAffineLineExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.EtaleSmoothDualityTensor
import WeilConjectures.AlgebraicGeometry.SmoothLisseRelativeDual
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleLocal
import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale
import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion

/-! # A compact dual model for smooth ordinary direct images

Source: blueprint lemma-smooth-morphisms-locally-constant-sheaves, construction of the compact
coefficient dual and compatibility with ordinary exchange.
-/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Use the standard derived functor through its API, including inside the pullback alias.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor

/-- The total derived inverse image, with coefficient parameters kept generic.
This is definitionally `L(upperStar A v)`.
(auxiliary; not a blueprint node). -/
noncomputable abbrev smoothCompactPullback
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {S T : Scheme.{u}} (v : T ⟶ S) :
    _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology A) :=
  L(upperStar A v)

/-- A sheaf placed in degree zero, with generic coefficient instances. -/
noncomputable abbrev smoothCompactSingle
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology A) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj L

/-- Data of a compact coefficient-dual presentation, including its exchange identity.
Source: blueprint lemma-smooth-morphisms-locally-constant-sheaves, compact-dual construction and
comparison of pairings (auxiliary; not a blueprint node). -/
structure SmoothCompactDualModel (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S X : Scheme.{u}} (f : X ⟶ S)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) where
  complex : DerivedCategoryModule Λ S
  boundedConstructible : DerivedCategory.isBoundedConstructible Λ S complex
  openIso : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
    IsPullback p fU f U.ι →
    ((R(lowerStar (ModuleCat.{u + 1} Λ) fU)).obj
        ((smoothCompactPullback (ModuleCat.{u + 1} Λ) p).obj
          (smoothCompactSingle (ModuleCat Λ) X L)) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) U.toScheme).obj
        (op ((smoothCompactPullback (ModuleCat.{u + 1} Λ) U.ι).obj complex))).obj
          (constantComplex Λ U.toScheme))
  testIso : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
    IsPullback p fU f U.ι →
    ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
      (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T),
    IsPullback vX fT fU v →
    ((R(lowerStar (ModuleCat.{u + 1} Λ) fT)).obj
        ((smoothCompactPullback (ModuleCat.{u + 1} Λ) vX).obj
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) p).obj
            (smoothCompactSingle (ModuleCat Λ) X L))) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) T).obj
        (op ((smoothCompactPullback (ModuleCat.{u + 1} Λ) v).obj
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) U.ι).obj complex)))).obj
            (constantComplex Λ T))
  exchange : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme)
    (sqU : IsPullback p fU f U.ι)
    (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
    (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
    (sq : IsPullback vX fT fU v),
    (smoothCompactPullback (ModuleCat.{u + 1} Λ) v).map (openIso U XU p fU sqU).hom ≫
        finiteLisseDualPullbackComparison v
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) U.ι).obj complex) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) p).obj
            (smoothCompactSingle (ModuleCat Λ) X L)) ≫
        (testIso U XU p fU sqU T v XT vX fT sq).hom

open MonoidalCategory MonoidalClosed
open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem model_bounded_iff (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.isBoundedConstructible Λ T K ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hvan⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩,
      fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hvan i (Or.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i
        (lt_of_le_of_lt (le_max_right _ _) hi)

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem modelConstructibleCover (Λ : Type (u + 1)) [CommRing Λ] :
    ∀ (n : ℕ) {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (U : Fin n → X.Opens) (_ : ∀ x, ∃ i, x ∈ U i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    (∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj F)) →
      IsConstructibleSheaf F := by
  intro n
  induction n with
  | zero =>
    intro X _ U hU F _
    have : IsEmpty X := ⟨fun x ↦ by obtain ⟨i, -⟩ := hU x; exact i.elim0⟩
    exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
  | succ n ih =>
    intro X _ U hU F h
    have : TopologicalSpace.NoetherianSpace (U 0) :=
      (U 0).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U 0).ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    rw [Scheme.isConstructibleSheaf_iff_upperStar (U 0).ι (U 0).closedComplement (by simp)]
    refine ⟨h 0, ?_⟩
    let i := (U 0).closedComplement
    have : TopologicalSpace.NoetherianSpace _ := i.isClosedEmbedding.isInducing.noetherianSpace
    refine ih (fun k ↦ i ⁻¹ᵁ U k.succ) (fun z ↦ ?_) _ (fun k ↦ ?_)
    · have hz : i.base z ∉ U 0 := by
        have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
        rwa [(U 0).range_closedComplement] at this
      obtain ⟨k, hk⟩ := hU (i.base z)
      obtain ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ k |>.resolve_left (by rintro rfl; exact hz hk)
      exact ⟨k, hk⟩
    · have := h k.succ
      have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) (i ∣_ U k.succ)).obj F) :=
        IsConstructibleSheaf.upperStar (i ∣_ U k.succ)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι).obj F)
      exact IsConstructibleSheaf.of_iso
        (((Etale.upperStarComp _ (i ∣_ U k.succ) (U k.succ).ι).app F).symm ≪≫
          eqToIso (by rw [morphismRestrict_ι]) ≪≫
          (Etale.upperStarComp _ (i ⁻¹ᵁ U k.succ).ι i).app F)

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
open ZeroObject in
/-- A bounded complex whose restrictions to a finite open cover are bounded constructible
is bounded constructible. -/
private theorem modelBoundedCover (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ i, boundedConstructible (ModuleCat.{u + 1} Λ) (U i)
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X R := by
  -- homology commutes with the restrictions
  have e (i : Fin n) (q : ℤ) :=
    ((((U i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app R
  refine ⟨?_, fun q ↦ ?_⟩
  · choose c d hcd using fun i ↦
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 (h i).1
    -- a zero sheaf is detected on the cover
    have hz (q : ℤ) (hq : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R))) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
      have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
        (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
        (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
          isIso_of_source_target_iso_zero _ ((hq i.down).of_iso (e i.down q)).isoZero
            (Functor.map_isZero _ (isZero_zero _)).isoZero)
      exact (isZero_zero _).of_iso
        (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))
    refine (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded R).1
      ⟨-∑ i, |c i|, ∑ i, |d i|, ?_, ?_⟩
    · refine (_root_.DerivedCategory.isGE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isGE_iff _ (c i)).1 (hcd i).1 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |c i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := neg_abs_le (c i)
      omega
    · refine (_root_.DerivedCategory.isLE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isLE_iff _ (d i)).1 (hcd i).2 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |d i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := le_abs_self (d i)
      omega
  · refine modelConstructibleCover Λ n U hU _ fun i ↦ ?_
    have : IsConstructibleSheaf ((D(((U i).ι)^*[ModuleCat.{u + 1} Λ]) ⋙
        _root_.DerivedCategory.homologyFunctor _ q).obj R) := (h i).2 q
    exact IsConstructibleSheaf.of_iso (e i q).symm

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem modelPureDualizing (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V B : Scheme.{u}} (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] [HasInvertibleExponent Λ V] :
    DerivedCategory.boundedConstructibleFiniteTor Λ V
      (dualizingComplex Λ g) := by
  obtain ⟨L, hL, hstalk, ⟨e⟩, -⟩ := exists_dualizingComplex_iso_and_tensor_of_finite Λ g d
  have : IsFiniteSheaf L := ⟨fun Ω _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff _).2
    (Module.Finite.equiv (hstalk Ω s).some.toLinearEquiv.symm)⟩
  have : IsFiniteLocallyConstantSheaf L := { }
  have : IsConstructibleSheaf L := IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›
  have hflat : ObjectProperty.flat L := (flat_iff_forall_flat_sheafFiber_obj L).2 fun s ↦
    ObjectProperty.prop_of_iso _
      ((((pointSmallEtale s).uliftSheafFiberIso (ModuleCat.{u + 1} Λ)).app L ≪≫
        (hstalk _ s).some).symm)
      ((ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat Λ Λ)))
  have hL : DerivedCategory.boundedConstructibleFiniteTor Λ V
      (smoothCompactSingle (ModuleCat Λ) V L) :=
    ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat⟩⟩
  have hL₂ := hL.shift (2 * d : ℤ)
  exact ⟨(DerivedCategory.boundedConstructible _ V).prop_of_iso e.symm hL₂.1,
    (DerivedCategory.finiteTorAmplitude _ V).prop_of_iso e.symm hL₂.2⟩

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem modelOpenDualizing (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V B : Scheme.{u}} {U : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j] (g : V ⟶ B) [HasCompactification g]
    [HasCompactification (j ≫ g)] [QuasiCompact (j ≫ g)] :
    Nonempty ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g) ≅
      dualizingComplex Λ (j ≫ g)) := by
  have := HasCompactification.comp_of_isOpenImmersion (𝟙 V) j
  have : HasCompactification j := .of_eq (Category.comp_id j)
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j g
  exact ⟨(leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
    ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _).symm ≪≫ (c.app _).symm⟩

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private lemma modelQuasiCompact {Y Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y]
    (f : Y ⟶ Z) : QuasiCompact f :=
  ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem modelSmoothDualizing (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V B : Scheme.{u}} (g : V ⟶ B)
    [Smooth g] [HasCompactification g] [HasInvertibleExponent Λ V]
    [TopologicalSpace.NoetherianSpace V] :
    DerivedCategory.isInvertible Λ V (dualizingComplex Λ g) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ V
        (dualizingComplex Λ g) := by
  -- an open cover of `V` on which `g` has constant relative dimension
  have hchart (x : V) : ∃ W : V.Opens, x ∈ W ∧ ∃ e, SmoothOfRelativeDimension e (W.ι ≫ g) := by
    obtain ⟨U, W, -, -, hx, e, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE g x
    refine ⟨W, hx, n, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι g e]
    exact smoothOfRelativeDimension_comp (n := n) (m := 0) _ _
  choose W hxW n hn using hchart
  -- on each member of the cover, `Lj^* ω_g ≅ ω_{g|W}` is invertible and in `D^b_{ctf}`
  have hloc (x : V) :
      DerivedCategory.isInvertible Λ (W x)
          ((L(((W x).ι)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g)) ∧
        DerivedCategory.boundedConstructibleFiniteTor Λ (W x)
          ((L(((W x).ι)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g)) := by
    have : TopologicalSpace.NoetherianSpace (W x) :=
      (W x).ι.isOpenEmbedding.isInducing.noetherianSpace
    have := modelQuasiCompact (W x).ι
    have := modelQuasiCompact ((W x).ι ≫ g)
    have := HasCompactification.comp_of_isOpenImmersion g (W x).ι
    have : HasInvertibleExponent Λ (W x) := .of_hom (W x).ι
    have := hn x
    obtain ⟨e⟩ := modelOpenDualizing Λ (W x).ι g
    have h := modelPureDualizing Λ (n x) ((W x).ι ≫ g)
    exact ⟨DerivedCategory.isInvertible.of_iso e.symm
        (by
          obtain ⟨P, _, hP, ⟨eP⟩, -⟩ :=
            exists_dualizingComplex_iso_and_tensor_of_finite Λ ((W x).ι ≫ g) (n x)
          exact DerivedCategory.isInvertible.of_iso eP.symm
            (isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf P hP _)),
      (DerivedCategory.boundedConstructible _ (W x)).prop_of_iso e.symm h.1,
      (DerivedCategory.finiteTorAmplitude _ (W x)).prop_of_iso e.symm h.2⟩
  refine ⟨isInvertible_of_forall_isInvertible_leftDerivedUpperStar Λ (fun x ↦ (W x).ι)
    (fun x ↦ ⟨x, ⟨x, hxW x⟩, rfl⟩) fun x ↦ (hloc x).1, ?_⟩
  -- a finite subcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((W x : V.Opens) : Set V))
    (fun x ↦ (W x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let U (k : Fin t.card) : V.Opens := W (t.equivFin.symm k)
  have hU (y : V) : ∃ k, y ∈ U k := by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨t.equivFin ⟨x, hx⟩, by simpa [U] using hy⟩
  have hctf (k : Fin t.card) :
      DerivedCategory.boundedConstructible _ (U k)
          (D(((U k).ι)^*[ModuleCat.{u + 1} Λ]).obj (dualizingComplex Λ g)) ∧
        DerivedCategory.finiteTorAmplitude _ (U k)
          (D(((U k).ι)^*[ModuleCat.{u + 1} Λ]).obj (dualizingComplex Λ g)) :=
    let e := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (U k).ι).app
      (dualizingComplex Λ g)
    ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso e (hloc (t.equivFin.symm k)).2.1,
      (DerivedCategory.finiteTorAmplitude _ _).prop_of_iso e (hloc (t.equivFin.symm k)).2.2⟩
  refine ⟨modelBoundedCover Λ U hU _ fun k ↦ (hctf k).1, ?_⟩
  choose a b hab using fun k ↦ (hctf k).2
  refine ⟨-∑ k, |a k|, ∑ k, |b k|,
    torAmplitudeIn_of_openCover (ModuleCat.{u + 1} Λ) U hU _ fun k ↦ ?_⟩
  have ha := Finset.single_le_sum (f := fun k ↦ |a k|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ k)
  have hb := Finset.single_le_sum (f := fun k ↦ |b k|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ k)
  exact _root_.DerivedCategory.torAmplitudeIn.mono
    (by have := neg_abs_le (a k); linarith)
    (by have := le_abs_self (b k); linarith) (hab k)

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem modelExceptionalBaseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hfield : IsField Λ)
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    [Smooth f] [IsNoetherian X] [QuasiSeparatedSpace S] [HasInvertibleExponent Λ X]
    (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  classical
  have hchart (x : X) : ∃ W : X.Opens, x ∈ W ∧
      ∃ e, SmoothOfRelativeDimension e (W.ι ≫ f) := by
    obtain ⟨U, W, -, -, hx, e, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
    refine ⟨W, hx, n, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact smoothOfRelativeDimension_comp (n := n) (m := 0) _ _
  choose W hxW n hn using hchart
  have (x : X) : TopologicalSpace.NoetherianSpace (W x).toScheme :=
    (W x).ι.isOpenEmbedding.isInducing.noetherianSpace
  have (x : X) : QuasiCompact (W x).ι := modelQuasiCompact _
  have (x : X) : HasCompactification ((W x).ι ≫ f) :=
    HasCompactification.comp_of_isOpenImmersion f _
  have (x : X) : HasCompactification (pullback.snd (W x).ι g' ≫ f') :=
    .of_isPullback ((IsPullback.of_hasPullback (W x).ι g').paste_vert sq)
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover sq (fun x ↦ (W x).ι)
    (fun x ↦ pullback.snd (W x).ι g') (fun x ↦ pullback.fst (W x).ι g')
    (fun x ↦ IsPullback.of_hasPullback _ _) (fun x' ↦ ?_) K (fun x ↦ ?_)
  · have hx' : x' ∈ Set.range (pullback.snd (W (g'.base x')).ι g') := by
      rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
      exact hxW (g'.base x')
    obtain ⟨y, hy⟩ := hx'
    exact ⟨_, y, hy⟩
  · have : HasInvertibleExponent Λ (W x).toScheme := .of_hom (W x).ι
    have := hn x
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_affineLine Λ
      (compactModelAffineLineExchange Λ hfield) ((W x).ι ≫ f) (n x)
      ((IsPullback.of_hasPullback (W x).ι g').paste_vert sq)
    infer_instance

section GenericCalculus

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

@[irreducible]
private noncomputable def modelDualIsoGeneric
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [IsIso (projectionMap A f)]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G)
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (e : K ≅ ((derivedHom A X).obj (op N)).obj (G.obj Q)) :
    (R(lowerStar A f)).obj K ≅
      ((derivedHom A S).obj (op ((rightDerivedLowerShriek A f).obj N))).obj Q :=
  (R(lowerStar A f)).mapIso e ≪≫
    ((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q

@[irreducible]
private noncomputable def modelPullDualIsoGeneric
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (N K W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (hN : smoothRelativeDualizable A X N)
    (e : K ≅ ((derivedHom A X).obj (op N)).obj W)
    (d : (L(upperStar A g')).obj W ≅ W') :
    (L(upperStar A g')).obj K ≅
      ((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).obj W' := by
  let : BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
    _root_.DerivedCategory.braidedCategory' _
  letI : HasRightDual N := Classical.choice hN
  letI := BraidedCategory.exactPairing_swap N Nᘁ
  have := isIso_derivedHomUpperStarComparison_of_exactPairing A g' Nᘁ N W
  exact (L(upperStar A g')).mapIso e ≪≫
    asIso (derivedHomUpperStarComparison A g' N W) ≪≫
      ((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).mapIso d

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private noncomputable def modelPullDualIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hN : smoothRelativeDualizable (ModuleCat Λ) X N)
    [IsIso (dualizingComplexBaseChangeMap Λ sq)]
    (e : K ≅ ((derivedHom (ModuleCat Λ) X).obj (op N)).obj
      (dualizingComplex Λ f)) :
    (smoothCompactPullback (ModuleCat Λ) g').obj K ≅
      ((derivedHom (ModuleCat Λ) X').obj
        (op ((smoothCompactPullback (ModuleCat Λ) g').obj N))).obj
          (dualizingComplex Λ f') :=
  modelPullDualIsoGeneric (ModuleCat Λ) g' N K (dualizingComplex Λ f)
    (dualizingComplex Λ f') hN e (asIso (dualizingComplexBaseChangeMap Λ sq))

@[irreducible]
private noncomputable def modelBaseIsoGeneric
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (_adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (Q' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (hN : smoothRelativeDualizable A X N)
    (e : K ≅ ((derivedHom A X).obj (op N)).obj (G.obj Q))
    (d : (L(upperStar A g')).obj (G.obj Q) ≅
      G'.obj Q') :
    (R(lowerStar A f')).obj ((L(upperStar A g')).obj K) ≅
      ((derivedHom A S').obj
        (op ((L(upperStar A g)).obj ((rightDerivedLowerShriek A f).obj N)))).obj Q' :=
  modelDualIsoGeneric A f' adj' _ _ Q' (modelPullDualIsoGeneric A g' N K _ _ hN e d) ≪≫
    ((derivedHom A S').mapIso (asIso (B.app N)).op).app Q'

private theorem modelDualIsoGeneric_hom
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [IsIso (projectionMap A f)]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G)
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (e : K ≅ ((derivedHom A X).obj (op N)).obj (G.obj Q)) :
    (modelDualIsoGeneric A f adj N K Q e).hom =
      (R(lowerStar A f)).map e.hom ≫
        ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) := by
  unfold modelDualIsoGeneric
  rfl

private theorem modelPullDualIsoGeneric_hom
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (N K W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (W' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (hN : smoothRelativeDualizable A X N)
    (e : K ≅ ((derivedHom A X).obj (op N)).obj W)
    (d : (L(upperStar A g')).obj W ≅ W') :
    (modelPullDualIsoGeneric A g' N K W W' hN e d).hom =
      (L(upperStar A g')).map e.hom ≫ derivedHomUpperStarComparison A g' N W ≫
        ((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map d.hom := by
  unfold modelPullDualIsoGeneric
  rfl

private theorem modelBaseIsoGeneric_hom
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (Q' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (hN : smoothRelativeDualizable A X N)
    (e : K ≅ ((derivedHom A X).obj (op N)).obj (G.obj Q))
    (d : (L(upperStar A g')).obj (G.obj Q) ≅
      G'.obj Q') :
    (modelBaseIsoGeneric A adj adj' B N K Q Q' hN e d).hom =
      (modelDualIsoGeneric A f' adj' _ _ Q' (modelPullDualIsoGeneric A g' N K _ _ hN e d)).hom ≫
        (((derivedHom A S').mapIso (asIso (B.app N)).op).app Q').hom := by
  unfold modelBaseIsoGeneric
  rfl

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem modelTransportCore
    {C : Type*} [Category C] {A B C' D E F G H I J E' D' : C}
    (x : A ⟶ B) (a : B ⟶ C') (b : C' ⟶ D) (c : D ⟶ E)
    (d : B ⟶ F) (e : F ⟶ G) (f : G ⟶ H) (g : H ⟶ E)
    (h : A ⟶ I) (y : I ⟶ F) (z : H ⟶ J) (i : J ⟶ E')
    (j : E ⟶ E') (l : D ⟶ D') (k : D' ⟶ E')
    (hc : a ≫ b ≫ c = d ≫ e ≫ f ≫ g)
    (he : x ≫ d = h ≫ y) (ha : z ≫ i = g ≫ j) (hn : l ≫ k = c ≫ j) :
    x ≫ a ≫ b ≫ l ≫ k = h ≫ y ≫ e ≫ f ≫ z ≫ i := by
  calc
    _ = x ≫ (a ≫ b ≫ c) ≫ j := by simp only [Category.assoc, hn]
    _ = x ≫ (d ≫ e ≫ f ≫ g) ≫ j := by rw [hc]
    _ = (x ≫ d) ≫ e ≫ f ≫ (g ≫ j) := by simp only [Category.assoc]
    _ = (h ≫ y) ≫ e ≫ f ≫ (z ≫ i) := by rw [he, ← ha]
    _ = _ := by simp only [Category.assoc]

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem modelUnitExchangeAux
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (sq : CommSq g' f' f g)
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (Q' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (w : (L(upperStar A g)).obj Q ⟶ Q')
    (e : K ⟶ ((derivedHom A X).obj (op N)).obj (G.obj Q))
    (E : G ⋙ L(upperStar A g') ⟶
      L(upperStar A g) ⋙ G')
    (hcore :
      (L(upperStar A g)).map
          ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        (((derivedHom A S').map (inv (B.app N)).op).app
          ((L(upperStar A g)).obj Q)) =
      (derivedBaseChangeMap A sq).app _ ≫
        (R(lowerStar A f')).map
          (derivedHomUpperStarComparison A g' N (G.obj Q)) ≫
        (R(lowerStar A f')).map
          (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map (E.app Q)) ≫
        ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
          (op ((L(upperStar A g')).obj N))).app
            ((L(upperStar A g)).obj Q)).hom)) :
    (L(upperStar A g)).map ((R(lowerStar A f)).map e) ≫
      (L(upperStar A g)).map
        ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
      derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
      ((derivedHom A S').obj
        (op ((L(upperStar A g)).obj ((rightDerivedLowerShriek A f).obj N)))).map w ≫
      (((derivedHom A S').map (inv (B.app N)).op).app Q') =
    (derivedBaseChangeMap A sq).app K ≫
      (R(lowerStar A f')).map
        ((L(upperStar A g')).map e ≫
          derivedHomUpperStarComparison A g' N (G.obj Q) ≫
          ((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map
            ((E.app Q) ≫
              G'.map w)) ≫
      ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
        (op ((L(upperStar A g')).obj N))).app Q').hom) := by
  let C' := (rightDerivedLowerShriek A f').obj ((L(upperStar A g')).obj N)
  have hn := (((derivedHom A S').map (inv (B.app N)).op).naturality w)
  have ha : (R(lowerStar A f')).map
      (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map
        (G'.map w)) ≫
      ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
        (op ((L(upperStar A g')).obj N))).app Q').hom) =
      ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
        (op ((L(upperStar A g')).obj N))).app ((L(upperStar A g)).obj Q)).hom) ≫
      ((derivedHom A S').obj (op C')).map w :=
    (((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
      (op ((L(upperStar A g')).obj N))).hom.naturality w)
  have he := (derivedBaseChangeMap A sq).naturality e
  dsimp only [Functor.comp_map] at he
  have ht := modelTransportCore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcore he ha hn
  dsimp only [Functor.comp_obj, Functor.op_obj] at ht hn he
  simpa only [Functor.map_comp, Category.assoc] using ht

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize in
private theorem modelBaseIsoGeneric_exchange
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (sq : CommSq g' f' f g)
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (Q' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (w : (L(upperStar A g)).obj Q ⟶ Q')
    (e : K ≅ ((derivedHom A X).obj (op N)).obj (G.obj Q))
    (hN : smoothRelativeDualizable A X N)
    (d : (L(upperStar A g')).obj (G.obj Q) ≅
      G'.obj Q')
    (E : G ⋙ L(upperStar A g') ⟶
      L(upperStar A g) ⋙ G')
    (hcore :
      (L(upperStar A g)).map
          ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        (((derivedHom A S').map (inv (B.app N)).op).app
          ((L(upperStar A g)).obj Q)) =
      (derivedBaseChangeMap A sq).app _ ≫
        (R(lowerStar A f')).map
          (derivedHomUpperStarComparison A g' N (G.obj Q)) ≫
        (R(lowerStar A f')).map
          (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map (E.app Q)) ≫
        ((((derivedHomLowerShriekIsoOfAdjunction A f' adj').app
          (op ((L(upperStar A g')).obj N))).app ((L(upperStar A g)).obj Q)).hom))
    (hd : d.hom = E.app Q ≫ G'.map w) :
    (L(upperStar A g)).map (modelDualIsoGeneric A f adj N K Q e).hom ≫
      derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
      ((derivedHom A S').obj
        (op ((L(upperStar A g)).obj ((rightDerivedLowerShriek A f).obj N)))).map w =
    (derivedBaseChangeMap A sq).app K ≫
      (modelBaseIsoGeneric A adj adj' B N K Q Q' hN e d).hom := by
  let b := ((derivedHom A S').mapIso (asIso (B.app N)).op).app Q'
  rw [modelBaseIsoGeneric_hom]
  change _ = (derivedBaseChangeMap A sq).app K ≫
    ((modelDualIsoGeneric A f' adj' _ _ Q'
      (modelPullDualIsoGeneric A g' N K _ _ hN e d)).hom ≫ b.hom)
  conv_rhs => rw [← Category.assoc]
  apply (Iso.comp_inv_eq b).1
  have h := modelUnitExchangeAux A adj adj' sq B N K Q Q' w e.hom E hcore
  rw [modelDualIsoGeneric_hom, modelDualIsoGeneric_hom, modelPullDualIsoGeneric_hom]
  dsimp only [b, Iso.app_inv, Functor.mapIso_inv, Iso.op_inv, asIso_inv]
  simp only [Functor.map_comp, Category.assoc, hd] at h ⊢
  exact h

private theorem modelExchangeCompactIsoGeneric
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : S' ⟶ S} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f']
    [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (sq : CommSq g' f' f g)
    (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
      L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
    (N K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (Q' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (w : (L(upperStar A g)).obj Q ⟶ Q')
    (e : K ≅ ((derivedHom A X).obj (op N)).obj (G.obj Q))
    (hN : smoothRelativeDualizable A X N)
    (d : (L(upperStar A g')).obj (G.obj Q) ≅
      G'.obj Q')
    (E : G ⋙ L(upperStar A g') ⟶
      L(upperStar A g) ⋙ G')
    (hcore : compactInternalAdjunctionExchangeSquare A adj adj' sq B N Q E)
    (hd : d.hom = E.app Q ≫ G'.map w)
    (M : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (b : M ≅ (rightDerivedLowerShriek A f).obj N) :
    CommSq
      ((L(upperStar A g)).map
        (modelDualIsoGeneric A f adj N K Q e ≪≫ ((derivedHom A S).mapIso b.op).app Q).hom)
      ((derivedBaseChangeMap A sq).app K)
      (derivedHomUpperStarComparison A g M Q ≫
        ((derivedHom A S').obj (op ((L(upperStar A g)).obj M))).map w)
      (modelBaseIsoGeneric A adj adj' B N K Q Q' hN e d ≪≫
        ((derivedHom A S').mapIso ((L(upperStar A g)).mapIso b).op).app Q').hom := by
  constructor
  have hc := (compactInternalAdjunctionExchangeSquare_iff A adj adj' sq B N Q E).1 hcore
  have hb := modelBaseIsoGeneric_exchange A adj adj' sq B N K Q Q' w e hN d E hc hd
  have hn : (L(upperStar A g)).map (((derivedHom A S).map b.hom.op).app Q) ≫
      (derivedHomUpperStarComparison A g M Q ≫
        ((derivedHom A S').obj (op ((L(upperStar A g)).obj M))).map w) =
      (derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        ((derivedHom A S').obj
          (op ((L(upperStar A g)).obj ((rightDerivedLowerShriek A f).obj N)))).map w) ≫
        ((derivedHom A S').map ((L(upperStar A g)).map b.hom).op).app Q' := by
    simp only [Category.assoc]
    erw [derivedHomUpperStarComparison_naturality_left_assoc]
    congr 1
    exact (((derivedHom A S').map ((L(upperStar A g)).map b.hom).op).naturality w).symm
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.op_hom,
    Functor.map_comp, Category.assoc]
  rw [hn, ← Category.assoc, hb, Category.assoc]

end GenericCalculus

attribute [local instance high] SymmetricCategory.toBraidedCategory in
attribute [local instance 20000] Etale.sheafBraidedCategory in
private theorem modelDualizablePull
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hN : smoothRelativeDualizable A X N) :
    smoothRelativeDualizable A Y ((L(upperStar A g)).obj N) := by
  let := leftDerivedUpperStarMonoidal A g
  exact (show IsDualizable N from hN).map (L(upperStar A g))

private noncomputable def modelPush
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {S T : Scheme.{u}} (v : T ⟶ S) :
    _root_.DerivedCategory (Sheaf T.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) :=
  R(lowerStar A v)

/-- Keep an explicitly constructed image object behind a small generic interface. -/
@[irreducible]
private noncomputable def modelImage {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (N : C) : D := F.obj N

private noncomputable def modelImageIso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (N : C) : modelImage F N ≅ F.obj N := by
  unfold modelImage
  exact Iso.refl _

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem modelImage_bounded
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (k : Type u) [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f]
    (N : DerivedCategoryModule Λ X)
    (hNc : DerivedCategory.boundedConstructibleFiniteTor Λ X N) :
    DerivedCategory.isBoundedConstructible Λ S
      (modelImage (rightDerivedLowerShriek (ModuleCat Λ) f) N) := by
  unfold modelImage
  exact (model_bounded_iff Λ S _).2
    (boundedConstructible_rightDerivedLowerShriek_and_isIso Λ f (f ≫ aS) aS rfl N hNc.1).1

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
attribute [local instance] isIso_projectionMap_of_finite in
attribute [local instance] isIso_rightDerivedLowerShriekBaseChangeMap in
/-- Assemble the model from an explicit relative dual and its compact image. -/
@[irreducible]
private noncomputable def modelFromDual
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hfield : IsField Λ)
    {S X : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f] [Smooth f]
    [IsNoetherian S] [IsNoetherian X] [HasInvertibleExponent Λ X]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (N : DerivedCategoryModule Λ X) (hN : smoothRelativeDualizable (ModuleCat Λ) X N)
    (τ : smoothCompactSingle (ModuleCat Λ) X L ≅
      ((derivedHom (ModuleCat Λ) X).obj (op N)).obj
        (dualizingComplex Λ f))
    (C : DerivedCategoryModule Λ S)
    (ciso : C ≅ (rightDerivedLowerShriek (ModuleCat Λ) f).obj N)
    (hC : DerivedCategory.isBoundedConstructible Λ S C) :
    SmoothCompactDualModel Λ f L := by
  classical
  let K := smoothCompactSingle (ModuleCat Λ) X L
  let hU (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X)
      (fU : XU ⟶ U.toScheme) (sqU : IsPullback p fU f U.ι) :
      Σ' eU : (modelPush (ModuleCat Λ) fU).obj
          ((smoothCompactPullback (ModuleCat Λ) p).obj K) ≅
        ((derivedHom (ModuleCat Λ) U.toScheme).obj
          (op ((smoothCompactPullback (ModuleCat Λ) U.ι).obj C))).obj
            (constantComplex Λ U.toScheme),
      ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
        (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
        (sq : IsPullback vX fT fU v),
      Σ' eT : (modelPush (ModuleCat Λ) fT).obj
          ((smoothCompactPullback (ModuleCat Λ) vX).obj
            ((smoothCompactPullback (ModuleCat Λ) p).obj K)) ≅
        ((derivedHom (ModuleCat Λ) T).obj
          (op ((smoothCompactPullback (ModuleCat Λ) v).obj
            ((smoothCompactPullback (ModuleCat Λ) U.ι).obj C)))).obj
              (constantComplex Λ T),
      (smoothCompactPullback (ModuleCat Λ) v).map eU.hom ≫
        finiteLisseDualPullbackComparison v ((smoothCompactPullback (ModuleCat Λ) U.ι).obj C) =
      (derivedBaseChangeMap (ModuleCat Λ) sq.toCommSq).app
          ((smoothCompactPullback (ModuleCat Λ) p).obj K) ≫ eT.hom := by
    have : HasCompactification fU := .of_isPullback sqU
    have : QuasiCompact fU := MorphismProperty.of_isPullback sqU inferInstance
    have : Smooth fU := MorphismProperty.of_isPullback sqU inferInstance
    have : IsOpenImmersion p := MorphismProperty.of_isPullback sqU.flip inferInstance
    have : IsLocallyNoetherian XU := isLocallyNoetherian_of_isOpenImmersion p
    have : TopologicalSpace.NoetherianSpace XU :=
      p.isOpenEmbedding.isInducing.noetherianSpace
    have : IsNoetherian XU := ⟨⟩
    have : TopologicalSpace.NoetherianSpace U.toScheme :=
      U.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : IsNoetherian U.toScheme := ⟨⟩
    have : HasInvertibleExponent Λ XU := .of_hom p
    have := modelExceptionalBaseChange Λ hfield sqU
    have : IsIso (dualizingComplexBaseChangeMap Λ sqU) :=
      (isIso_dualizingComplexBaseChangeMap_iff Λ sqU).2 inferInstance
    let NU := (smoothCompactPullback (ModuleCat Λ) p).obj N
    let KU := (smoothCompactPullback (ModuleCat Λ) p).obj K
    let τU := modelPullDualIso Λ sqU N K hN τ
    let CU := (smoothCompactPullback (ModuleCat Λ) U.ι).obj C
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqU
    let bU : CU ≅ (rightDerivedLowerShriek (ModuleCat Λ) fU).obj NU :=
      (smoothCompactPullback (ModuleCat Λ) U.ι).mapIso ciso ≪≫
        asIso ((rightDerivedLowerShriekBaseChangeMap Λ sqU).app N)
    let dU := ((derivedHom (ModuleCat Λ) U.toScheme).mapIso bU.op).app (𝟙_ _)
    refine ⟨modelDualIsoGeneric (ModuleCat Λ) fU
      (rightDerivedUpperShriekAdjunction Λ fU) NU KU (𝟙_ _) τU ≪≫ dU, ?_⟩
    intro T _ v XT vX fT sq
    have : HasCompactification fT := .of_isPullback sq
    have : QuasiCompact fT := MorphismProperty.of_isPullback sq inferInstance
    have := modelExceptionalBaseChange Λ hfield sq
    have : IsIso (dualizingComplexBaseChangeMap Λ sq) :=
      (isIso_dualizingComplexBaseChangeMap_iff Λ sq).2 inferInstance
    have hNU : smoothRelativeDualizable (ModuleCat Λ) XU NU :=
      modelDualizablePull (ModuleCat Λ) p N hN
    let dT := ((derivedHom (ModuleCat Λ) T).mapIso
      ((smoothCompactPullback (ModuleCat Λ) v).mapIso bU).op).app (𝟙_ _)
    let B := rightDerivedLowerShriekBaseChangeMap Λ sq
    let d := asIso (dualizingComplexBaseChangeMap Λ sq)
    refine ⟨modelBaseIsoGeneric (ModuleCat Λ)
      (rightDerivedUpperShriekAdjunction Λ fU) (rightDerivedUpperShriekAdjunction Λ fT) B NU KU
      (𝟙_ _) (𝟙_ _) hNU τU d ≪≫ dT, ?_⟩
    have hc := compactInternalAdjunctionExchange Λ sq NU (𝟙_ _)
    have hd : d.hom = (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
        (rightDerivedUpperShriek Λ fT).map
          (leftDerivedUpperStarUnitIso (ModuleCat Λ) v).hom := rfl
    have he := modelExchangeCompactIsoGeneric (ModuleCat Λ)
      (rightDerivedUpperShriekAdjunction Λ fU) (rightDerivedUpperShriekAdjunction Λ fT)
      sq.toCommSq B NU KU
      (𝟙_ _) (𝟙_ _) (leftDerivedUpperStarUnitIso (ModuleCat Λ) v).hom τU hNU d
      (rightDerivedUpperShriekBaseChangeMap Λ sq) hc hd CU bU
    exact he.w
  exact {
    complex := C
    boundedConstructible := hC
    openIso := fun U XU p fU sqU ↦ (hU U XU p fU sqU).fst
    testIso := fun U XU p fU sqU T _ v XT vX fT sq ↦
      ((hU U XU p fU sqU).snd T v XT vX fT sq).fst
    exchange := fun U XU p fU sqU T _ v XT vX fT sq ↦
      ((hU U XU p fU sqU).snd T v XT vX fT sq).snd }

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
attribute [local instance] isIso_projectionMap_of_finite in
attribute [local instance] isIso_rightDerivedLowerShriekBaseChangeMap in
/-- Compact relative-dual models exist for finite field coefficients. -/
private theorem modelForFiniteField
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hfield : IsField Λ)
    (k : Type u) [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    Nonempty (SmoothCompactDualModel Λ f L) := by
  classical
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : IsNoetherian S := ⟨⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : HasInvertibleExponent Λ X := .of_hom (f ≫ aS)
  have := hL
  have hωall := modelSmoothDualizing Λ f
  have hω := hωall.1
  have hωc := hωall.2
  let K := smoothCompactSingle (ModuleCat Λ) X L
  let N := smoothRelativeDual (ModuleCat Λ) X K (dualizingComplex Λ f)
  have hdual := finiteLisseRelativeDual Λ hfield X L hL
    (dualizingComplex Λ f) hω hωc
  have hN := hdual.1
  have hNc := hdual.2.1
  have hτ := hdual.2.2
  let τ : K ≅ ((derivedHom (ModuleCat Λ) X).obj (op N)).obj
      (dualizingComplex Λ f) :=
    asIso (smoothRelativeBidualMap (ModuleCat Λ) X (dualizingComplex Λ f) K)
  let C := modelImage (rightDerivedLowerShriek (ModuleCat Λ) f) N
  let ciso : C ≅ (rightDerivedLowerShriek (ModuleCat Λ) f).obj N :=
    modelImageIso (rightDerivedLowerShriek (ModuleCat Λ) f) N
  have hC := modelImage_bounded Λ k S aS X f N hNc
  exact ⟨modelFromDual Λ hfield f L N hN τ C ciso hC⟩

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
attribute [local instance] isIso_projectionMap_of_finite in
attribute [local instance] isIso_rightDerivedLowerShriekBaseChangeMap in
/-- The relative compact dual of a finite local system has bounded constructible compact
image. Ordinary direct image is its coefficient dual, compatibly with the actual exchange.
This assertion makes no generic shrinking and asserts no local constancy of a direct image.

Source: blueprint sec-six-functors-basics/sk-lem-geo-smooth-generic/
lem-asd-smooth-generic-direct-image.proof.md, relative dual construction and exchange.
(auxiliary; not a blueprint node).

Proof: Cover the smooth source by charts of constant relative dimension. Smooth duality
makes the relative dualizing complex invertible and bounded constructible of finite Tor
amplitude on every chart. Invertibility is local, and a finite subcover supplies common
cohomological and Tor bounds globally. Put K=L[0], N=RHom(K,omega), and C=Rf_!N.
Relative finite-lisse biduality identifies K with RHom(N,omega); compact-support finiteness
makes C bounded constructible. Pull this presentation to each open restriction and each
Noetherian test scheme, using smooth exceptional exchange and dualizability of N.
Internal compact adjunction and the dual of compact exchange provide the required
isomorphisms. Cartesian compatibility of internal compact adjunction, naturality in the
coefficient unit, and naturality in compact exchange prove their exchange identity.
All complexes and comparison maps are the explicit constructions of the six-functor API. -/
theorem exists_smooth_compact_dual_model
    (k : Type u) [Field k] (S : Scheme.{u})
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    Nonempty (SmoothCompactDualModel (ULift.{u + 1} (ZMod ℓ)) f L) := by
  classical
  let Λ := ULift.{u + 1} (ZMod ℓ)
  have hchar : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓ.symm
  have : HasInvertibleExponent Λ (Spec (.of k)) := by
    refine ⟨ℓ, (Fact.out : ℓ.Prime).pos, ?_, ?_⟩
    · apply ULift.down_injective
      simp [Λ]
    · simpa only [map_natCast] using
        (Ne.isUnit hchar).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hfield : IsField Λ := Field.toIsField _
  exact modelForFiniteField Λ hfield k S aS X f L hL

end AlgebraicGeometry.Etale
