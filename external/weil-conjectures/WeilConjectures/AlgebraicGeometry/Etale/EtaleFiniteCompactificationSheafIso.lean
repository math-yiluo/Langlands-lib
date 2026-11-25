/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactificationGraphMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.Algebra.Homology.SingleHomology

/-!
# The sheaf graph comparison in a finite compactification

Source: Stacks Project, Tags 0GKM, 0F4Y and 015F
(blueprint: lem-sfb-etale-finite-compactification-sheaf-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem singleMap_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E G : C ⥤ D) [E.Additive] [G.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : E ⟶ G) (M : C) :
    (E.mapCochainComplexSingleFunctor 0).inv.app M ≫
      (a.mapHomologicalComplex (.up ℤ)).app ((CochainComplex.singleFunctor C 0).obj M) ≫
      (G.mapCochainComplexSingleFunctor 0).hom.app M =
      (CochainComplex.singleFunctor D 0).map (a.app M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    change ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).inv.app M ≫
      (a.mapHomologicalComplex (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M).f 0 =
        ((HomologicalComplex.single D (.up ℤ) 0).map (a.app M)).f 0
    simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).eq_of_src _ _

/-- Localization of termwise maps detects an isomorphism of exact functors. -/
private theorem isIso_of_isIso_Q_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory D]
    (E G : C ⥤ D) [E.Additive] [G.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : E ⟶ G)
    (hq : ∀ K : CochainComplex C ℤ,
      IsIso (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app K))) :
    IsIso a := by
  have happ (M : C) : IsIso (a.app M) := by
    let S := CochainComplex.singleFunctor C 0
    have := hq (S.obj M)
    have hs : (E.mapCochainComplexSingleFunctor 0).inv.app M ≫
          (a.mapHomologicalComplex (.up ℤ)).app (S.obj M) ≫
          (G.mapCochainComplexSingleFunctor 0).hom.app M =
        (CochainComplex.singleFunctor _ 0).map (a.app M) :=
      singleMap_naturality E G a M
    have hh : IsIso (DerivedCategory.Q.map
        ((CochainComplex.singleFunctor _ 0).map (a.app M))) := by
      rw [← hs, Functor.map_comp, Functor.map_comp]
      infer_instance
    let S' := CochainComplex.singleFunctor D 0
    have hqi : QuasiIso (S'.map (a.app M)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso D _).mp hh
    have h₀ : IsIso ((S' ⋙ HomologicalComplex.homologyFunctor _ (.up ℤ) 0).map
        (a.app M)) := by
      exact (quasiIsoAt_iff_isIso_homologyMap _ 0).mp inferInstance
    exact (NatIso.isIso_map_iff
      (HomologicalComplex.homologyFunctorSingleIso _ (.up ℤ) 0) (a.app M)).mp h₀
  exact NatIso.isIso_of_isIso_app a

private theorem isIso_middle
    {C : Type*} [Category C] {W X Y Z : C}
    (l : W ⟶ X) (m : X ⟶ Y) (r : Y ⟶ Z) [IsIso l] [IsIso r]
    (h : IsIso (l ≫ m ≫ r)) : IsIso m := by
  have := h
  have : IsIso (m ≫ r) := IsIso.of_isIso_comp_left l _
  exact IsIso.of_isIso_comp_right _ r

private theorem isIso_of_derived_comparison
    {C B D : Type*} [Category C] [Category B] [Category D]
    [Abelian C] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions B]
    (E : C ⥤ D) (F : C ⥤ B) (G : B ⥤ D)
    [E.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : E ⟶ F ⋙ G)
    (t : E.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    [IsIso t]
    (ht : ∀ K : HomotopyCategory C (.up ℤ),
      t.app (DerivedCategory.Qh.obj K) =
        E.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K) ≫
        G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.inv.app K)) :
    IsIso a := by
  apply isIso_of_isIso_Q_map E (F ⋙ G) a
  intro K
  let KH := (HomotopyCategory.quotient _ (.up ℤ)).obj K
  have hh : IsIso (t.app (DerivedCategory.Qh.obj KH)) := inferInstance
  rw [ht KH] at hh
  have htail : IsIso (DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app KH) ≫
    G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj KH) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.inv.app KH)) := by
    infer_instance
  have hmiddle : IsIso (DerivedCategory.Qh.map
      ((a.mapHomotopyCategory (.up ℤ)).app KH)) :=
    isIso_middle (E.mapDerivedCategoryFactorsh.hom.app KH) _ _ hh
  dsimp only [KH] at hmiddle
  rw [NatTrans.mapHomotopyCategory_app] at hmiddle
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).mp hmiddle

/-- In a compactification with finite proper part, the sheaf graph map for a separated
quasi-compact etale map is invertible. This follows by applying degree-zero detection to
the normalized unbounded graph comparison, since the finite pushforward is exact.
Source: Stacks Project, Tags 0GKM, 0F4Y and 015F
(blueprint: lem-sfb-etale-finite-compactification-sheaf-iso).

Proof: the derived graph map is invertible. On a homotopy representative its formula
is the termwise sheaf graph map followed by the finite-pushforward derived unit and the
localization factorization isomorphisms. The latter factors are invertible, hence the
termwise sheaf graph map becomes invertible after localization. Evaluate on the complex
concentrated in degree zero at an arbitrary sheaf. The termwise map identifies, through
the canonical single-complex isomorphisms, with the single of the original sheaf map.
A quasi-isomorphism induces an invertible degree-zero homology map, and the homology
of a single complex is its sheaf. Thus every component
of the sheaf graph map is invertible, proving invertibility of the transformation. -/
theorem isIso_etaleCompactificationGraphMap_of_isFinite
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    (c : Compactification f) [IsFinite c.g] :
    IsIso (etaleCompactificationGraphMap A f c) := by
  have := isIso_compactSupportGraphDerivedComparison A f c
  exact isIso_of_derived_comparison
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (lowerStar (ModuleCat.{u + 1} A) c.g)
    (etaleCompactificationGraphMap A f c)
    (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
    (compactSupportDerivedComparison_app A f c (etaleCompactificationGraphMap A f c))

end AlgebraicGeometry.Etale
