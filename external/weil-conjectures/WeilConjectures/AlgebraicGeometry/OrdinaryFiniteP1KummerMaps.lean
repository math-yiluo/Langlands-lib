/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# The two Kummer-normalized projective-line components

Source: blueprint lemma-cohomology-projective-line-trace and its proof.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option maxRecDepth 2000

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedUpperStarLowerStarAdjunction commShiftLeftDerivedUpperStar
  leftDerivedUpperStarIsoMapDerivedCategory Functor.CommShift.ofIso

attribute [local irreducible] leftDerivedUpperStarComp
  singleFunctorCompLeftDerivedUpperStarIso

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] ordinaryFiniteClassCore
  HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀
  CategoryTheory.Abelian.Ext.mapExactFunctor

attribute [local irreducible] Scheme.finiteEtaleTateLine ordinaryFiniteRootMap
  ordinaryFiniteTensor AlgebraicGeometry.ProjectiveSpace Scheme.rootsOfUnitySheaf
  ProjectiveSpace.twist
  ordinaryFiniteP1ChernSpec ordinaryFiniteP1Exchange
  ordinaryFiniteP1DecompositionSourceMap
  ordinaryFiniteP1Unit ordinaryFiniteP1ChernPushforward

set_option allowUnsafeReducibility true in
attribute [local reducible] ordinaryFiniteDegreeZero ordinaryFiniteLine ordinaryFiniteUnit

local instance (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePullback A f).Additive := additive_leftDerivedUpperStar (ModuleCat.{u + 1} A) f

local instance (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePushforward A f).Additive :=
  additive_rightDerivedLowerStar (ModuleCat.{u + 1} A) f

local instance (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePushforward A f).PreservesZeroMorphisms := by infer_instance

attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward

/-- A family of projective-line Chern arrows on Noetherian bases.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
abbrev OrdinaryFiniteP1ChernFamily (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) :=
  ∀ (S : Scheme.{u}) [IsNoetherian S], IsUnit (N : Γ(S, ⊤)) →
    (ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The Chern family represents the actual scalar-extended Kummer boundary of O(1).
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
def OrdinaryFiniteP1ChernFamilySpec (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (c : OrdinaryFiniteP1ChernFamily A N hA) : Prop :=
  ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    ordinaryFiniteP1ChernSpec A N hA S
      (affineTraceProjectiveInvertible N S hS) (c S hS)

/-- The specified twisted-unit and Chern components, before proving invertibility.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1KummerMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (c : OrdinaryFiniteP1ChernFamily A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
    (ordinaryFiniteP1ChernPushforward A N hA S (c S hS))

/-- The decomposition square uses the exact ordinary-etale exchange of the item.
Source: blueprint lemma-cohomology-projective-line-trace, base-change assertion.
(auxiliary; not a blueprint node). -/
def OrdinaryFiniteP1KummerMapBaseChange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (c : OrdinaryFiniteP1ChernFamily A N hA) : Prop :=
  ∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))),
    (ordinaryFinitePullback A f).map (ordinaryFiniteP1KummerMap A N hA t c S hS) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (affineTraceProjectiveInvertible N S hS)).hom =
      ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
        ordinaryFiniteP1KummerMap A N hA t c S' hS'

/-- Compute the divisor degree of O(1) from its two-chart cohomology. -/
private theorem p1_twist_degree_one (k : Type u) [Field k] :
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1).degree k = 1 := by
  have hchi (d : ℕ) :
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d).eulerChar k =
        (d + 1 : ℕ) := by
    obtain ⟨e⟩ := ProjectiveLine.nonempty_H_zero_twist_equiv k d
    let b := (ProjectiveSpace.homogeneousSubmoduleBasis (ULift.{u} (Fin 2)) k d).reindex
      (ProjectiveLine.degreeEqEquivFin d)
    have hzero : Scheme.Modules.finrankH k
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) 0 = d + 1 := by
      rw [Scheme.Modules.finrankH, e.finrank_eq, Module.finrank_eq_card_basis b]
      simp
    have := ProjectiveLine.subsingleton_H_one_twist k d (by omega)
    have hone : Scheme.Modules.finrankH k
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) d) 1 = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [Scheme.Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one, hzero, hone]
    simp
  unfold Scheme.Modules.degree
  rw [Scheme.Modules.eulerChar_congr k
    (ProjectiveSpace.unitIsoTwistZero (ULift.{u} (Fin 2)) (Spec (.of k)))]
  have h1 := hchi 1
  have h0 := hchi 0
  simp only [Nat.cast_one] at h1
  simp only [Nat.cast_zero] at h0
  rw [h1, h0]
  norm_num

/-- The degree-normalized Kummer isomorphism sends the actual class of O(1) to one.
Source: Curve.RootsOfUnityTop.sheafHTwoTrace and the two-chart computation of O(d).
(auxiliary; not a blueprint node).
Proof: the Kummer trace is bijective and takes a line bundle's boundary to its degree
modulo N. The two-chart cohomology of O(d) gives Euler characteristic d+1 for d>=0.
Since the unit is O(0), O(1) has degree 2-1=1. Substitute this in the trace equation. -/
theorem ordinaryFiniteP1_geometric_kummer_normalization
    (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ) (hN : (N : k) ≠ 0)
    (hP : IsUnit (N : Γ(ProjectiveLine (Spec (.of k)), ⊤))) :
    ∃ e : Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 2 ≃+ ZMod N,
      e ((ProjectiveLine (Spec (.of k))).kummerδ₁ N hP
        (Scheme.Pic.toCohomologicalPicardGroup (ProjectiveLine (Spec (.of k)))
          (Scheme.Pic.ofIsInvertible
            (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1)))) = 1 := by
  have : NeZero N := ⟨by intro h; simp [h] at hN⟩
  have hgeom := ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hgeom.1
  have := hgeom.2.1
  have : ConnectedSpace (ProjectiveLine (Spec (.of k))) :=
    IsConnectedCurve.connectedSpace
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : GeometricallyIntegral
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    GeometricallyIntegral.of_isSepClosed
  let e := AddEquiv.ofBijective
    (Scheme.sheafHTwoTrace (k := k) (X := ProjectiveLine (Spec (.of k))) N hN)
    (Scheme.bijective_sheafHTwoTrace N hN)
  refine ⟨e, ?_⟩
  change Scheme.sheafHTwoTrace (k := k) (X := ProjectiveLine (Spec (.of k))) N hN
    (Scheme.picToSheafHTwo N hN (Additive.ofMul (Scheme.Pic.ofIsInvertible
      (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1)))) = 1
  rw [Scheme.sheafHTwoTrace_picToSheafHTwo]
  change (((Scheme.picDegreeHom k _ (Scheme.Pic.ofIsInvertible
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) 1))).toAdd : ℤ) : ZMod N) = 1
  rw [Scheme.picDegreeHom_ofIsInvertible, p1_twist_degree_one]
  simp

/-- On an algebraically closed geometric fibre the root sheaf has cohomology only
in degrees zero and two, both cyclic of order N. The isomorphisms here do not yet
normalize the actual Chern arrow.
Source: ProjectiveLineGenusZero and Curve.Estimate, the geometric-fibre part of
blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: apply the proper-curve calculation to the genus-zero projective line. Its
first cohomology is a function group on Fin 0, hence zero. A primitive root
identifies the constant Z/N sheaf with the root sheaf in every degree; transport
these computations along the induced cohomology isomorphisms. -/
theorem ordinaryFiniteP1_geometric_cohomology (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : (N : k) ≠ 0) :
    Nonempty (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 0 ≃+
      ZMod N) ∧
    Subsingleton (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 1) ∧
    Nonempty (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) 2 ≃+
      ZMod N) ∧
    ∀ q : ℕ, 2 < q →
      Subsingleton (Sheaf.H ((ProjectiveLine (Spec (.of k))).rootsOfUnitySheaf N) q) := by
  obtain ⟨hcurve, hsmooth, hproper, hgenus, _⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have := hsmooth
  have := hproper
  obtain ⟨hzero, hone, htwo, hhigher⟩ :=
    IsConnectedCurve.sheafH_constantZMod_of_isProper
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) N hN
  have transport (q : ℕ) :=
    Scheme.nonempty_addEquiv_sheafH_constantZMod_rootsOfUnitySheaf
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) N hN q
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := transport 0
    obtain ⟨e0⟩ := hzero
    exact ⟨e.symm.trans e0⟩
  · obtain ⟨e⟩ := transport 1
    obtain ⟨e1⟩ := hone
    have htriv : Subsingleton
        (Sheaf.H ((ProjectiveLine (Spec (.of k))).constantZMod N) 1) := by
      rw [hgenus, mul_zero] at e1
      exact e1.toEquiv.subsingleton
    exact e.symm.toEquiv.subsingleton
  · obtain ⟨e⟩ := transport 2
    obtain ⟨e2⟩ := htwo
    exact ⟨e.symm.trans e2⟩
  · intro q hq
    obtain ⟨e⟩ := transport q
    have := hhigher q hq
    exact e.symm.toEquiv.subsingleton

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_biprod_square
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} {X' Y' Z' : D}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z')
    (e : F.obj X ⟶ X') (e' : F.obj Y ⟶ Y') (v : F.obj Z ⟶ Z')
    (ha : F.map a ≫ v = e ≫ a') (hb : F.map b ≫ v = e' ≫ b') :
    F.map (biprod.desc a b) ≫ v =
      biprod.lift (F.map biprod.fst ≫ e) (F.map biprod.snd ≫ e') ≫
        biprod.desc a' b' := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  apply (cancel_epi (F.mapBiprod X Y).inv).mp
  apply biprod.hom_ext' <;>
    simp [← Functor.map_comp_assoc, ha, hb]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem isIso_biprod_lift_map
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {X' Y' : D}
    (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') :
    IsIso (biprod.lift (F.map (biprod.fst : X ⊞ Y ⟶ X) ≫ e₁.hom)
      (F.map (biprod.snd : X ⊞ Y ⟶ Y) ≫ e₂.hom)) := by
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  let e := F.mapBiprod X Y ≪≫ biprod.mapIso e₁ e₂
  have he : e.hom = biprod.lift (F.map (biprod.fst : X ⊞ Y ⟶ X) ≫ e₁.hom)
      (F.map (biprod.snd : X ⊞ Y ⟶ Y) ≫ e₂.hom) := by
    apply biprod.hom_ext
    · simp only [e, Iso.trans_hom, Category.assoc, biprod.mapIso_hom,
        biprod.map_fst, Functor.mapBiprod_hom, biprod.lift_fst_assoc, biprod.lift_fst]
    · simp only [e, Iso.trans_hom, Category.assoc, biprod.mapIso_hom,
        biprod.map_snd, Functor.mapBiprod_hom, biprod.lift_snd_assoc, biprod.lift_snd]
  rw [← he]
  infer_instance

section
attribute [local irreducible] moduleAbelianUpperStarIso
set_option allowUnsafeReducibility true in
attribute [local semireducible] Scheme.rootsOfUnitySheaf

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_isIso_desc_left
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z)
    (hY : IsZero (F.obj Y)) (ha : IsIso (F.map a)) :
    IsIso (F.map (biprod.desc a b)) := by
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hinl : IsIso (biprod.inl : F.obj X ⟶ F.obj X ⊞ F.obj Y) := by
    refine ⟨⟨biprod.fst, by simp, ?_⟩⟩
    apply biprod.hom_ext'
    · simp
    · exact hY.eq_of_src _ _
  have hcomp : (F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b) =
      biprod.desc (F.map a) (F.map b) := by
    apply biprod.hom_ext' <;>
      simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        ← Functor.map_comp, biprod.inl_desc, biprod.inr_desc]
  have : IsIso (biprod.desc (F.map a) (F.map b)) := by
    have : IsIso ((biprod.inl : F.obj X ⟶ F.obj X ⊞ F.obj Y) ≫
        biprod.desc (F.map a) (F.map b)) := by simpa using ha
    exact IsIso.of_isIso_comp_left biprod.inl _
  have : IsIso ((F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.mapBiprod X Y).inv _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_isIso_desc_right
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z)
    (hX : IsZero (F.obj X)) (hb : IsIso (F.map b)) :
    IsIso (F.map (biprod.desc a b)) := by
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hinr : IsIso (biprod.inr : F.obj Y ⟶ F.obj X ⊞ F.obj Y) := by
    refine ⟨⟨biprod.snd, by simp, ?_⟩⟩
    apply biprod.hom_ext'
    · exact hX.eq_of_src _ _
    · simp
  have hcomp : (F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b) =
      biprod.desc (F.map a) (F.map b) := by
    apply biprod.hom_ext' <;>
      simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        ← Functor.map_comp, biprod.inl_desc, biprod.inr_desc]
  have : IsIso (biprod.desc (F.map a) (F.map b)) := by
    have : IsIso ((biprod.inr : F.obj Y ⟶ F.obj X ⊞ F.obj Y) ≫
        biprod.desc (F.map a) (F.map b)) := by simpa using hb
    exact IsIso.of_isIso_comp_left biprod.inr _
  have : IsIso ((F.mapBiprod X Y).inv ≫ F.map (biprod.desc a b)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.mapBiprod X Y).inv _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_isIso_biprod_of_homology
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {U V K : DerivedCategory C} (a : V ⟶ K) (b : U ⟶ K)
    (hU : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj U))
    (hV : ∀ n : ℤ, n ≠ -2 → IsZero ((DerivedCategory.homologyFunctor C n).obj V))
    (hK : ∀ n : ℤ, n ≠ 0 → n ≠ -2 →
      IsZero ((DerivedCategory.homologyFunctor C n).obj K))
    (hb : IsIso ((DerivedCategory.homologyFunctor C 0).map b))
    (ha : IsIso ((DerivedCategory.homologyFunctor C (-2)).map a)) :
    IsIso (biprod.desc a b) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  let H := DerivedCategory.homologyFunctor C n
  by_cases hn0 : n = 0
  · subst n
    exact kummer_isIso_desc_right (DerivedCategory.homologyFunctor C 0) a b
      (hV 0 (by norm_num)) hb
  · by_cases hn2 : n = -2
    · subst n
      exact kummer_isIso_desc_left (DerivedCategory.homologyFunctor C (-2)) a b
        (hU (-2) (by norm_num)) ha
    · have hzU := hU n hn0
      have hzV := hV n hn2
      have hzK := hK n hn0 hn2
      apply IsZero.isIso _ hzK
      let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
      apply IsZero.of_iso _ (H.mapBiprod V U)
      rw [IsZero.iff_id_eq_zero]
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
        first | exact hzU.eq_of_src _ _ | exact hzV.eq_of_src _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_isIso_of_square_core
    {C : Type*} [Category C] {U V W X Y : C}
    (a : U ⟶ V) (b : V ⟶ W) (d : W ⟶ X) (e : U ⟶ Y) (f : Y ⟶ X)
    [IsIso b] [IsIso d] [IsIso e] [IsIso f]
    (h : a ≫ b ≫ d = e ≫ f) : IsIso a := by
  have : IsIso (a ≫ (b ≫ d)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right a (b ≫ d)

private theorem kummer_p1_constant_vanishing
    (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ) (hNk : (N : k) ≠ 0)
    (B : AddCommGrpCat.{u + 1}) [Finite B] (hB : ∀ b : B, N • b = 0)
    (q : ℕ) (hq0 : q ≠ 0) (hq2 : q ≠ 2) :
    Subsingleton (Sheaf.H ((constantSheaf
      (ProjectiveLine (Spec (.of k))).smallEtaleTopology AddCommGrpCat.{u + 1}).obj B) q) := by
  let P := ProjectiveLine (Spec (.of k))
  exact (constantSheaf P.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    Sheaf.functorH P.smallEtaleTopology q).subsingleton_obj_of_zmod N
      (fun m hm ↦ by
        have hm' := AffineSpace.natCast_ne_zero_of_dvd hm hNk
        obtain ⟨e⟩ := AffineSpace.nonempty_constantZModIsoRootsOfUnitySheaf
          (P ↘ Spec (.of k)) hm'
        have hcoh := ordinaryFiniteP1_geometric_cohomology k m hm'
        have hz : Subsingleton (Sheaf.H (P.rootsOfUnitySheaf m) q) := by
          by_cases hq1 : q = 1
          · subst q; exact hcoh.2.1
          · exact hcoh.2.2.2 q (by omega)
        exact @Equiv.subsingleton _ _
          ((Sheaf.functorH P.smallEtaleTopology q).mapIso e).addCommGroupIsoToAddEquiv.toEquiv
            hz) B hB

private theorem kummer_isIso_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    IsIso (C := DerivedCategoryModule A S') (ordinaryFiniteP1Exchange A f M) :=
  isIso_ordinaryFiniteP1Exchange A f M

private theorem kummer_isIso_sourceMap
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (C := DerivedCategoryModule A S')
      (ordinaryFiniteP1DecompositionSourceMap A N hA t f hS) := by
  have : (ordinaryFinitePullback A (X := S') (Y := S) f).Additive := by
    infer_instance
  unfold ordinaryFiniteP1DecompositionSourceMap
  exact isIso_biprod_lift_map (ordinaryFinitePullback A (X := S') (Y := S) f)
    (X := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
    (Y := ordinaryFiniteUnit A S)
    (ordinaryFiniteShiftedLinePullback A N hA t f hS) (ordinaryFiniteUnitPullback A f)

private theorem kummer_geometric_conservative
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S : Scheme.{u}}
    {K L : DerivedCategoryModule A S} (a : K ⟶ L)
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      IsIso ((ordinaryFinitePullback A s).map a)) : IsIso a := by
  rw [DerivedCategory.isIso_iff]
  intro i
  apply isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
    (fun s ↦ S.algClosurePoint s)
    (fun s ↦ ⟨s, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩)
  intro s
  have hs := h _ (S.algClosurePoint s)
  have : IsIso ((upperStar (ModuleCat.{u + 1} A) (S.algClosurePoint s)).leftDerivedFunctor.map
    a) := by
    with_unfolding_all
      exact hs
  apply (NatIso.isIso_map_iff
    (leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} A)
      (S.algClosurePoint s) i) a).2
  change IsIso ((DerivedCategory.homologyFunctor _ i).map
    ((upperStar (ModuleCat.{u + 1} A) (S.algClosurePoint s)).leftDerivedFunctor.map a))
  infer_instance

private theorem kummer_unit_split_mono
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (π : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ π = 𝟙 Y)
    (M : DerivedCategoryModule A Y) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) π).unit.app M) := by
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) π).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) σ)
  let e : (upperStar (ModuleCat.{u + 1} A) π).leftDerivedFunctor ⋙
      (upperStar (ModuleCat.{u + 1} A) σ).leftDerivedFunctor ≅ 𝟭 _ :=
    (leftDerivedUpperStarComp _ σ π (𝟙 Y) hσ.symm).symm ≪≫ leftDerivedUpperStarId _ Y
  have : ((upperStar (ModuleCat.{u + 1} A) π).leftDerivedFunctor ⋙
      (upperStar (ModuleCat.{u + 1} A) σ).leftDerivedFunctor).Full :=
    Functor.Full.of_iso e.symm
  have : ((upperStar (ModuleCat.{u + 1} A) π).leftDerivedFunctor ⋙
      (upperStar (ModuleCat.{u + 1} A) σ).leftDerivedFunctor).Faithful :=
    Functor.Faithful.of_iso e.symm
  have h := Adjunction.comp_unit_app (derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) π) (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) σ) M
  refine ⟨⟨(lowerStar (ModuleCat.{u + 1} A) π).rightDerivedFunctor.map
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) σ).unit.app _) ≫
      inv (adj.unit.app M), ?_⟩⟩
  rw [← Category.assoc, ← h, IsIso.hom_inv_id]

private theorem kummer_chern_component_square
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (cFamily : OrdinaryFiniteP1ChernFamily A N hA)
    (hcFamily : OrdinaryFiniteP1ChernFamilySpec A N hA cFamily)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) :
    (ordinaryFinitePullback A f).map
        (ordinaryFiniteP1ChernPushforward A N hA S (cFamily S hS)) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (affineTraceProjectiveInvertible N S hS)).hom =
      (ordinaryFiniteUnitPullback A f).hom ≫
        ordinaryFiniteP1ChernPushforward A N hA S' (cFamily S' hS') := by
  exact ordinaryFiniteP1_chern_adjunct_baseChange A N hN hA t f hS hS'
    (cFamily S hS) (cFamily S' hS') (hcFamily S hS) (hcFamily S' hS')

private theorem kummer_unit_component_square
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) :
    (ordinaryFinitePullback A f).map (ordinaryFiniteP1Unit A N hA t S hS) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (affineTraceProjectiveInvertible N S hS)).hom =
      (ordinaryFiniteShiftedLinePullback A N hA t f hS).hom ≫
        ordinaryFiniteP1Unit A N hA t S' hS' := by
  exact ordinaryFiniteP1_twisted_unit_baseChange A N hN hA t f hS hS'

private theorem kummer_baseChange
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (cFamily : OrdinaryFiniteP1ChernFamily A N hA)
    (hcFamily : OrdinaryFiniteP1ChernFamilySpec A N hA cFamily)
     :
    OrdinaryFiniteP1KummerMapBaseChange A N hA t cFamily := by
  intro S' S _ _ f hS hS'
  have : (ordinaryFinitePullback A f).Additive := by
    infer_instance
  unfold ordinaryFiniteP1KummerMap ordinaryFiniteP1DecompositionSourceMap
  exact kummer_biprod_square (ordinaryFinitePullback A f) _ _ _ _ _ _ _
    ((kummer_unit_component_square N hN A hA t) f hS hS')
    ((kummer_chern_component_square N hN A hA t cFamily hcFamily) f hS hS')

private theorem kummer_p1_h2_scalar_generator
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (hP : IsUnit (N : Γ(ProjectiveLine (Spec (.of k)), ⊤))) :
    Function.Bijective (fun a : A ↦ Sheaf.H.map
      ((moduleAbelianForget A (ProjectiveLine (Spec (.of k)))).map
        (a • 𝟙 (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec (.of k))) N A hA))) 2
      (ordinaryFiniteP1KummerClass A N hA (Spec (.of k)) hP)) := by
  exact ordinaryFiniteP1KummerClass_scalar_bijective_of_normalization N A hA k hNk hP
    (ordinaryFiniteP1_geometric_kummer_normalization k N hNk hP)

private theorem kummer_chern_faithful
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (hS : IsUnit (N : Γ(Spec (.of k), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (Spec (.of k))) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (Spec (.of k))))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (Spec (.of k))
      (affineTraceProjectiveInvertible N _ hS) c) :
    ∀ a : A, (DerivedCategory.singleFunctor _ 0).map
      (a • 𝟙 (ordinaryFiniteConstant A (Spec (.of k)))) ≫
      ordinaryFiniteP1ChernPushforward A N hA (Spec (.of k)) c = 0 → a = 0 := by
  exact ordinaryFiniteP1ChernPushforward_scalar_faithful N A hA (Spec (.of k))
    (affineTraceProjectiveInvertible N _ hS) c hc
    ((kummer_p1_h2_scalar_generator N A hA) k hNk (affineTraceProjectiveInvertible N _ hS)).1

private theorem kummer_p1_unit_mono_homology
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
     (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor _ n).map
      (ordinaryFiniteP1Unit A N hA t S hS)) := by
  have hs := (kummer_unit_split_mono A) (ProjectiveLine S ↘ S)
    (ProjectiveLine.infinity S) (ProjectiveLine.infinity_over (S := S))
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
  unfold ordinaryFiniteP1Unit ordinaryFinitePushforward
  let H := DerivedCategory.homologyFunctor
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n
  have hu : IsSplitMono (H.map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (ProjectiveLine S ↘ S)).unit.app
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧))) :=
    IsSplitMono.mk' (hs.exists_splitMono.some.map H)
  have hv : IsIso (H.map
      ((lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)).rightDerivedFunctor.map
        (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine S ↘ S) hS).hom)) :=
    (H.mapIso
    (((lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)).rightDerivedFunctor).mapIso
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine S ↘ S) hS))).isIso_hom
  unfold ordinaryFinitePullback at hv
  rw [Functor.map_comp]
  apply CategoryTheory.mono_comp'
  · exact hu.exists_splitMono.some.mono
  · exact @IsIso.mono_of_iso _ _ _ _ _ hv

private theorem kummer_fibre_line_trivial
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k]
     (hNk : (N : k) ≠ 0) :
    Nonempty (Scheme.finiteEtaleTateLine (Spec (.of k)) N A hA ≅
      ordinaryFiniteConstant A (Spec (.of k))) := by
  exact (kummer_line_as_constant N A hA) k (𝟙 (Spec (.of k))) hNk

private theorem kummer_fibre_target_card
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
     (n : ℤ) (hn : n = 0 ∨ n = -2) :
    Nonempty (
      ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj
        ((DerivedCategory.homologyFunctor _ n).obj
          ((ordinaryFinitePushforward A
            (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).obj
              ((ordinaryFiniteLine A N hA
                (ProjectiveLine (Spec (.of k))))⟦(2 : ℤ)⟧)))) ≃ A) := by
  exact ordinaryFiniteP1_fibre_target_card N A hA k hNk
    (fun hP ↦ (kummer_p1_h2_scalar_generator N A hA) k hNk hP) n hn

private theorem kummer_fibre_target_vanishes
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
     (n : ℤ) (hn0 : n ≠ 0) (hn2 : n ≠ -2) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((ordinaryFinitePushforward A (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine (Spec (.of k))))⟦(2 : ℤ)⟧))) := by
  obtain ⟨hcurve, hsmooth, hproper, -, -⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have := hsmooth
  have := hproper
  let P := ProjectiveLine (Spec (.of k))
  have : CompactSpace P :=
    QuasiCompact.compactSpace_of_compactSpace (P ↘ Spec (.of k))
  have : QuasiSeparatedSpace P :=
    quasiSeparatedSpace_of_quasiSeparated (P ↘ Spec (.of k))
  let F := Scheme.finiteEtaleTateLine P N A hA
  let G := (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse
  apply (IsZero.iff_id_eq_zero _).2
  apply G.map_injective
  rw [G.map_id, G.map_zero]
  apply IsZero.eq_of_src
  by_cases hneg : 2 + n < 0
  · exact (isZero_cohomology_singleFunctor_of_neg A P F hneg).of_iso
      ((ordinaryFinitePushforward_single_shift_homology_iso A) k (P ↘ Spec (.of k)) F n (2 + n) rfl)
  · let q := (2 + n).toNat
    have hq : 2 + n = (q : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    apply IsZero.of_iso _ ((ordinaryFinitePushforward_single_shift_homology_iso A) k
      (P ↘ Spec (.of k)) F n q hq)
    rw [isZero_cohomology_singleFunctor_iff]
    obtain ⟨σ⟩ := (kummer_line_as_constant N A hA) k (P ↘ Spec (.of k)) hNk
    let τ := (moduleAbelianForget A P).mapIso σ ≪≫ forget₂SheafConstantSheafIso A P
    have hz := kummer_p1_constant_vanishing k N hNk
      ((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (ModuleCat.of A A))
      (fun a ↦ by change N • (a : A) = 0; rw [nsmul_eq_mul, hA, zero_mul])
      q (by omega) (by omega)
    exact @Equiv.subsingleton _ _
      ((Sheaf.functorH P.smallEtaleTopology q).mapIso τ).addCommGroupIsoToAddEquiv.toEquiv hz

private theorem kummer_fibre_source_line_equiv
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k]
     (hNk : (N : k) ≠ 0) :
    Nonempty (
      ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj
        ((DerivedCategory.homologyFunctor _ (-2)).obj
          ((ordinaryFiniteLine A N hA (Spec (.of k)))⟦(2 : ℤ)⟧))) ≃ A) := by
  obtain ⟨e⟩ := (kummer_fibre_line_trivial N A hA) k hNk
  let G := (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse
  let F := Scheme.finiteEtaleTateLine (Spec (.of k)) N A hA
  let H := DerivedCategory.homologyFunctor
    (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)) (-2)
  let sh := kummer_homology_shift_iso
    (ordinaryFiniteDegreeZero A (Spec (.of k)) F) (-2) 0 (by norm_num)
  let d := sh ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F ≪≫ e
  exact ⟨(CategoryTheory.Iso.toLinearEquiv
    (G.mapIso d ≪≫ ((constantSheafEquivalenceOfIsSepClosed A (k := k)).unitIso.app
      (ModuleCat.of A A)).symm)).toEquiv⟩

private theorem kummer_fibre_iso
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (cFamily : OrdinaryFiniteP1ChernFamily A N hA)
    (hcFamily : OrdinaryFiniteP1ChernFamilySpec A N hA cFamily)
    (k : Type u) [Field k] [IsAlgClosed k]
    (hS : IsUnit (N : Γ(Spec (.of k), ⊤))) :
    IsIso (ordinaryFiniteP1KummerMap A N hA t cFamily (Spec (.of k)) hS) := by
  have : NeZero N := ⟨hN.ne'⟩
  let S := Spec (.of k)
  have hNk : (N : k) ≠ 0 := by
    have h := hS.map (Scheme.ΓSpecIso (.of k)).hom.hom
    simpa only [map_natCast] using h.ne_zero
  let G := (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse
  let U := ordinaryFiniteUnit A S
  let V := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  let K := (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  have hU (n : ℤ) (hn : n ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj U) :=
    DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) hn
  have hV (n : ℤ) (hn : n ≠ -2) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj V) := by
    apply IsZero.of_iso
      (DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
        (Iso.refl (ordinaryFiniteLine A N hA S)) (show 2 + n ≠ 0 by omega))
    exact kummer_homology_shift_iso (ordinaryFiniteLine A N hA S) n (2 + n) rfl
  have hbIso : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (ordinaryFiniteP1ChernPushforward A N hA S (cFamily S hS))) := by
    have : Mono ((DerivedCategory.homologyFunctor _ 0).map
        (ordinaryFiniteP1ChernPushforward A N hA S (cFamily S hS))) :=
      (ordinaryFiniteUnit_mono_homology_zero A) k _
        ((kummer_chern_faithful N A hA) k hNk hS (cFamily S hS) (hcFamily S hS))
    obtain ⟨eU⟩ := (kummer_fibre_source_unit_equiv A) k
    obtain ⟨eK⟩ := (kummer_fibre_target_card N A hA) k hNk 0 (Or.inl rfl)
    have : Finite (G.obj ((DerivedCategory.homologyFunctor _ 0).obj U)) :=
      Finite.of_equiv A eU.symm
    have : Finite (G.obj ((DerivedCategory.homologyFunctor _ 0).obj K)) :=
      Finite.of_equiv A eK.symm
    exact (kummer_isIso_of_mono_card A) k
      ((DerivedCategory.homologyFunctor _ 0).map
        (ordinaryFiniteP1ChernPushforward A N hA S (cFamily S hS))) (by
      rw [Nat.card_congr eK, Nat.card_congr eU])
  have haIso : IsIso ((DerivedCategory.homologyFunctor _ (-2)).map
      (ordinaryFiniteP1Unit A N hA t S hS)) := by
    have := (kummer_p1_unit_mono_homology N A hA t) S hS (-2)
    obtain ⟨eV⟩ := (kummer_fibre_source_line_equiv N A hA) k hNk
    obtain ⟨eK⟩ := (kummer_fibre_target_card N A hA) k hNk (-2) (Or.inr rfl)
    have : Finite (G.obj ((DerivedCategory.homologyFunctor _ (-2)).obj V)) :=
      Finite.of_equiv A eV.symm
    have : Finite (G.obj ((DerivedCategory.homologyFunctor _ (-2)).obj K)) :=
      Finite.of_equiv A eK.symm
    exact (kummer_isIso_of_mono_card A) k
      ((DerivedCategory.homologyFunctor _ (-2)).map
        (ordinaryFiniteP1Unit A N hA t S hS)) (by
      rw [Nat.card_congr eK, Nat.card_congr eV])
  unfold ordinaryFiniteP1KummerMap
  exact kummer_isIso_biprod_of_homology
    (C := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ordinaryFiniteP1Unit A N hA t S hS)
    (ordinaryFiniteP1ChernPushforward A N hA S (cFamily S hS))
    hU hV (fun n h0 h2 ↦ (kummer_fibre_target_vanishes N A hA) k hNk n h0 h2) hbIso haIso

private theorem kummer_relative_iso
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (cFamily : OrdinaryFiniteP1ChernFamily A N hA)
    (hcFamily : OrdinaryFiniteP1ChernFamilySpec A N hA cFamily)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (ordinaryFiniteP1KummerMap A N hA t cFamily S hS) := by
  have : NeZero N := ⟨hN.ne'⟩
  apply (kummer_geometric_conservative A)
  intro k _ _ f
  let hS' : IsUnit (N : Γ(Spec (.of k), ⊤)) :=
    (map_natCast f.appTop.hom N) ▸ hS.map f.appTop.hom
  have hi := (kummer_fibre_iso N hN A hA t cFamily hcFamily) k hS'
  have he := (kummer_baseChange N hN A hA t cFamily hcFamily) f hS hS'
  have hs := (kummer_isIso_sourceMap N A hA t) f hS
  have hx := (kummer_isIso_exchange A) f
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  exact kummer_isIso_of_square_core _ _ _ _ _ he

/-- The Kummer-normalized two-component map is invertible and commutes with base change.
This concerns only cohomology and its two specified arrows; it asserts no duality adjunction.
Source: blueprint thm-amb-p1-decomposition.md and its proof, and the decomposition/trace
part of lem-asd-ordinary-finite-p1-adjunction, steps 2--4.
(auxiliary; not a blueprint node).

Proof: First use Z/N coefficients. At an algebraically closed geometric fibre the projective
line is a smooth proper connected genus-zero curve. Proper-curve cohomology gives Z/N in
degrees zero and two and zero otherwise. A primitive root identifies the root sheaf with
Z/N. The actual second Kummer boundary identifies H²(mu_N) with Pic/N. The split degree
sequence and divisibility of Pic⁰ identify Pic/N with Z/N, and O(1), the dual of the ideal
of one rational point, has degree one. Hence the Chern component is an isomorphism in
degree two, and the twisted unit is an isomorphism in degree zero. Proper exchange,
exact conservative geometric stalks and the unbounded cohomology criterion prove that
the two-component map is invertible over Z/N. Apply derived coefficient extension to A.
The proper finite-coefficient extension comparison is an isomorphism; flatness of mu_N
identifies the extended twist even when A is not flat over Z/N. Its mate normalization
identifies the unit component, and its scalar normalization identifies the Chern component.
This proves invertibility over A. For base change, pull back the infinity divisor. On its
chart its equation is a polynomial variable, hence remains a nonzerodivisor after arbitrary
base change, and its dual ideal is O(1). Naturality of the supported Kummer class gives
the pulled-back Chern arrow. The unit/exchange equation follows from the mate formula and
an adjunction triangle identity. Tensor/exchange coherence and the normalized line
comparison identify the two components. Additivity and the biproduct universal property
give exactly the displayed square. The zero ring (N=1) and empty base have zero objects
and satisfy the same assertions. -/
theorem ordinaryFiniteP1_kummer_maps (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c) :
    (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      IsIso (ordinaryFiniteP1KummerMap A N hA t c S hS)) ∧
    OrdinaryFiniteP1KummerMapBaseChange A N hA t c := by
  exact ⟨fun S _ hS ↦ kummer_relative_iso N hN A hA t c hc S hS,
    kummer_baseChange N hN A hA t c hc⟩

end

end AlgebraicGeometry.Etale
