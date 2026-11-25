/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullbackDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Inverse image on localizing categories

Source: blueprint main-20261015, chap-Construction-of-f,
sk-prop-proper-base-change-unbounded/sk-prop-proper-base-change-unbounded-pullback.md
(blueprint: proposition-proper-base-change-localizing-categories--1).

The restriction uses the ordinary unbounded derived module-object categories and the
constant-scalar-model definition of constructibility. No derived completion is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] unboundedLocalizingPullbackCommShift

private theorem pullback_exact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) :
    (CondensedRing.upperStar Λ g).leftDerivedFunctor.IsTriangulated := by
  let : (CondensedRing.upperStar Λ g).leftDerivedFunctor.CommShift ℤ :=
    unboundedLocalizingPullbackCommShift Λ g
  let e := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

private theorem pullback_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).PreservesFlat := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let R := condensedRingObj Λ Y
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  have h := inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
  let e : CondensedRing.upperStar Λ f ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  exact ⟨fun hM ↦ ObjectProperty.prop_of_iso ObjectProperty.flat
    (e.symm.app _) (h.flat_obj hM)⟩

private theorem pullback_tor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hK : DerivedCategory.finiteTorAmplitude _ K) :
    DerivedCategory.finiteTorAmplitude _
      ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K) := by
  let F := CondensedRing.upperStar Λ g
  obtain ⟨a, b, hK⟩ := hK
  obtain ⟨P, hPa, hPb, hP, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hK
  let P' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y')) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj P
  have : P'.IsStrictlyGE a := inferInstance
  have : P'.IsStrictlyLE b := inferInstance
  have hflat := pullback_flat Λ g
  have hP' : ∀ n, ObjectProperty.flat (P'.X n) :=
    fun n ↦ hflat.flat_obj (hP n)
  refine ⟨a, b, (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso ?_
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat P' a b hP')⟩
  exact (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm.app K

private theorem pullback_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((CondensedRing.upperStar Λ g).obj M) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, ite_eq_left hX, ite_eq_left hY] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  let T := S.pullback g
  refine ⟨T, fun i ↦ ?_⟩
  let q : T.domain i ⟶ S.domain i := pullback.fst (S.immersion i) g
  have comm : q ≫ S.immersion i = T.immersion i ≫ g := pullback.condition
  have h := pullback_finiteConstantLocalModel Λ q _ (hS i)
  let e := ((CondensedRing.upperStarComp Λ (T.immersion i) g).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
      comm.symm) ≪≫
    (CondensedRing.upperStarComp Λ q (S.immersion i)).app M
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun j ↦ by
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU j
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f j)).mapIso e ≪≫ eP⟩⟩⟩

private theorem pullback_bounded_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (h : ∀ M, IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((CondensedRing.upperStar Λ g).obj M))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hK : constantModelBoundedConstructible Λ Y K) :
    constantModelBoundedConstructible Λ Y'
      ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K) := by
  let F := CondensedRing.upperStar Λ g
  let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g
  have hi := (constantModelConstructibleFiniteTor_wellDefined Λ Y').1
  refine ⟨?_, fun n ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.symm.app K)
      (F.bounded_mapDerivedCategory_obj hK.1)
  · exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ Y')
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso (e.symm.app K)) (h _ (hK.2 n))

-- The full-subcategory and universe transports require explicit structural comparisons.
private theorem pullback_of_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (h : ∀ M, IsConstantModelConstructible Λ Y M →
      IsConstantModelConstructible Λ Y' ((CondensedRing.upperStar Λ g).obj M)) :
    Nonempty (UnboundedLocalizingPullback Λ g) := by
  let F := (CondensedRing.upperStar Λ g).leftDerivedFunctor
  let G : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :=
    constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _
  let G' : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y'))) :=
    constantModelBoundedConstructible Λ Y' ⊓ DerivedCategory.finiteTorAmplitude _
  obtain ⟨hsums, _, _, hs, _, _, _, _⟩ := localizingClosure_exists Λ Y G
  obtain ⟨hsums', _, _, ht, hgen, _, _, _⟩ := localizingClosure_exists Λ Y' G'
  let : HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) := hsums
  let : HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y'))) := hsums'
  let : F.IsTriangulated := pullback_exact Λ g
  let : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I) F := fun I ↦
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  let : (localizingClosureProEtale Λ Y).IsTriangulated := hs.1
  let : (localizingClosureProEtale Λ Y').IsTriangulated := ht.1
  let : (localizingClosureProEtale Λ Y').IsClosedUnderIsomorphisms := ht.2.1
  have hc : ∀ K, G K → G' (F.obj K) := fun K hK ↦
    ⟨pullback_bounded_constructible Λ g h K hK.1, pullback_tor Λ g K hK.2⟩
  have hm : ∀ K, localizingClosureProEtale Λ Y K →
      localizingClosureProEtale Λ Y' (F.obj K) := by
    intro K hK
    apply hK ((localizingClosureProEtale Λ Y').inverseImage F)
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro I D hD hmem
      let := hD
      apply ObjectProperty.prop_of_iso (localizingClosureProEtale Λ Y')
        (preservesColimitIso F D).symm
      exact ht.2.2 (D ⋙ F) inferInstance hmem
    · exact fun L hL ↦ hgen _ (hc L hL)
  let hm' := fun K : (localizingClosureProEtale Λ Y).FullSubcategory ↦ hm K.obj K.property
  let R := (localizingClosureProEtale Λ Y').lift
    ((localizingClosureProEtale Λ Y).ι ⋙ F) hm'
  have hrsmall (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) R := by
    let : (localizingClosureProEtale Λ Y).IsClosedUnderIsomorphisms := hs.2.1
    let : (localizingClosureProEtale Λ Y).IsClosedUnderColimitsOfShape (Discrete I) :=
      hs.isClosedUnderColimitsOfShape_discrete I
    have : PreservesColimitsOfShape (Discrete I) F :=
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have : PreservesColimitsOfShape (Discrete I)
        (R ⋙ (localizingClosureProEtale Λ Y').ι) :=
      preservesColimitsOfShape_of_natIso
        ((localizingClosureProEtale Λ Y').liftCompιIso _ hm').symm
    exact preservesColimitsOfShape_of_reflects_of_preserves R
      (localizingClosureProEtale Λ Y').ι
  refine ⟨{ exact := inferInstance
            sums := fun I ↦ inferInstance
            constructible := hc
            localizing := hm'
            restrictionExact := ?_
            restrictionSums := ?_ }⟩
  · infer_instance
  · exact fun I ↦ Functor.preservesColimitsOfShape_discrete_of_small R hrsmall I

-- Elaborating all six coefficient instances needs the same heartbeat budget.
/-- Exact inverse image preserves small sums, bounded constructible finite-Tor objects,
and their localizing closure, for each of the six admissible coefficient types.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: proposition-proper-base-change-localizing-categories--1).

Proof (the four steps of the node):

1. Transport exactness of the termwise derived inverse image along
   `leftDerivedUpperStarIsoMapDerivedCategory`, using the canonical shift structure
   above. The derived adjunction gives preservation of every existing coproduct.

2. The structure maps make both schemes quasi-compact and quasi-separated. Pull
   back a finite constructible stratification, and apply
   `pullback_finiteConstantLocalModel` to its strata. Composition isomorphisms
   identify the resulting inverse images. The exact-derived homology comparison
   and boundedness API then preserve bounded constructible complexes.

3. For every commutative condensed coefficient ring, represent a finite-Tor object
   by a bounded complex of flat modules using
   `DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn`. The coefficient
   comparison is invertible, so `inverseImageModule_preservesFlat` preserves its
   flat terms. The termwise inverse image retains the strict degree bounds.
   `DerivedCategory.torAmplitudeIn_Q_obj_of_flat` and the derived comparison
   therefore preserve Tor amplitude, uniformly for all six coefficient types.

4. The inverse image of the target localizing closure is localizing and contains
   the source generators. The defining intersection gives the object inclusion,
   and the full-subcategory lift inherits exactness. Closure under coproducts
   makes the source inclusion preserve them; the target inclusion reflects them.
   To cover the larger indexing universe, embed the nonzero support of any
   existing coproduct into its endomorphisms using coordinate idempotents. This
   support is small in the Hom universe. Shrink it and omit the zero summands to
   reduce preservation to the smaller coproducts. `localizingClosure_exists`
   supplies the ambient coproducts and the closure's triangulated structure.
-/
theorem unboundedLocalizingPullback
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    {Y' Y : Scheme.{u}} [Y'.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (g : Y' ⟶ Y) [g.IsOver (Spec (.of k))] :
    (∀ (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A],
      (∃ n : ℕ, (l ^ n : A) = 0) →
        Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj A) g)) ∧
    Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj ℤ_[l]) g) ∧
    Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj ℚ_[l]) g) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (UnboundedLocalizingPullback (Profinite.padicIntegersRingObj l E) g) ∧
      Nonempty (UnboundedLocalizingPullback (Profinite.continuousMapRingObj E) g)) ∧
    Nonempty (UnboundedLocalizingPullback (Profinite.padicAlgClRingObj l) g) := by
  have _ := hpl
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace
    (Y' ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    (quasiSeparated_iff_quasiSeparatedSpace (Y ↘ Spec (.of k))).mp inferInstance
  have : QuasiSeparatedSpace Y' :=
    (quasiSeparated_iff_quasiSeparatedSpace (Y' ↘ Spec (.of k))).mp inferInstance
  have H (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ] : Nonempty (UnboundedLocalizingPullback Λ g) :=
    pullback_of_constructible Λ g (pullback_constructible Λ g)
  exact ⟨fun _ _ _ _ _ _ ↦ H _, H _, H _, fun _ ↦ ⟨H _, H _⟩, H _⟩

end AlgebraicGeometry.ProEtale
