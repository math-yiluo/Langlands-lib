/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Fibre.FibreDimensionAfterBaseChange
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-!
# Proper direct-image bound for torsion étale sheaves

## References

* Stacks Project, Etale Cohomology, Tag 095U
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem localDim_homeomorph_le {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (x : A) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens A := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)

private theorem geometricFiber_dimension_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ Y) :
    topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  refine iSup_le fun x ↦ ?_
  let a := pullback.snd f y
  let j := a.fiberι (a x)
  have hj : Function.Surjective j := by
    intro z
    have hz : a z = a x := Subsingleton.elim _ _
    exact ⟨(a.fiberHomeo (a x)).symm ⟨z, hz⟩, a.fiberι_fiberHomeo_symm _ _⟩
  let e := (Equiv.ofBijective j ⟨j.isEmbedding.injective, hj⟩).toHomeomorphOfIsInducing
    j.isEmbedding.toIsInducing
  have hx : e (a.asFiber x) = x := a.fiberι_asFiber x
  have hlocal : topologicalKrullDimAt x ≤ topologicalKrullDimAt (a.asFiber x) := by
    have h := localDim_homeomorph_le e.symm (e (a.asFiber x))
    rw [Homeomorph.symm_apply_apply, hx] at h
    exact h
  exact hlocal.trans (((fibre_dimension_after_base_change f y x).2.2).le.trans
    ((le_iSup (fun z : f.fiber (f (pullback.fst f y x)) ↦ topologicalKrullDimAt z)
      (f.asFiber (pullback.fst f y x))).trans
      ((topologicalKrullDim_eq_iSup_topologicalKrullDimAt _).symm.le.trans (hd _))))

private theorem isZero_derivedSections_of_subsingleton_H {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H F q)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let S : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} := Sheaf.sectionsFunctorAt X.smallEtaleTopology (⊤_ X.Etale)
  have hS : IsZero ((S.rightDerived q).obj F) :=
    (Sheaf.subsingleton_H_iff_isZero_rightDerived X.smallEtaleTopology
      terminalIsTerminal q F).1 h
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).Additive := { map_add := rfl }
  exact hS.of_iso (Γ.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q ≪≫
    (NatIso.rightDerived (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{u + 1} terminalIsTerminal) q).app F)

private theorem globalSections_isEquivalence
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).IsEquivalence := by
  have h := (Scheme.geometricPoint_pullback_stalk Ω).1
  have : ((sheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))).IsEquivalence := h
  exact Functor.isEquivalence_of_iso
    (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
      AddCommGrpCat.{u + 1} (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) _)).symm

private theorem isZero_higherDirectImage_over_algClosed
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {T : Scheme.{u}}
    (a : T ⟶ Spec (.of Ω)) [LocallyOfFiniteType a] [QuasiCompact a]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)
    (q : ℕ) (hq : 2 * d < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} a).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  let Γ := Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Γ.IsEquivalence := globalSections_isEquivalence Ω
  have : (lowerStar AddCommGrpCat.{u + 1} a).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a)
  let L := (DerivedCategory.Plus.singleFunctor
    (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj G
  let R := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} a).obj L
  have hz := isZero_derivedSections_of_subsingleton_H G q
    (Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d a hd G hG q hq)
  let e := (Γ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app R).symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIso' (lowerStar AddCommGrpCat.{u + 1} a) Γ
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} a)).app L
  have hz' : IsZero (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj R)) :=
    hz.of_iso ((Γ.mapDerivedCategoryPlusHomologyFunctorIso q).app R ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso e)
  exact IsZero.of_full_of_faithful_of_isZero Γ _ hz'

private theorem torsionHomology_single {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    DerivedCategory.Plus.torsionHomology X ((DerivedCategory.Plus.singleFunctor _ 0).obj F) := by
  intro n
  by_cases hn : n = 0
  · subst n
    have : Scheme.IsTorsionSheaf ((𝟭 _).obj F) :=
      (Scheme.isTorsionSheaf_iff_isTorsion F).2 hF
    exact Scheme.IsTorsionSheaf.of_iso
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app F).symm
  · have hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n hn
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 n hn
    apply (Scheme.isTorsionSheaf_iff_isTorsion _).2
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro U x
    have hx := Functor.map_isZero
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ AddCommGrpCat.{u + 1}).obj U) hz
    have hs : Subsingleton _ := AddCommGrpCat.isZero_iff_subsingleton.mp hx
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨1, Nat.one_pos, ?_⟩
    simpa using hs.elim x 0

/-- For a proper morphism with fibre dimensions
at most `d`, every torsion abelian étale sheaf has zero higher direct image above `2 * d`. -/
theorem isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) (q : ℤ) (hq : 2 * (d : ℤ) < q) :
    IsZero
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  lift q to ℕ using (by omega)
  have hqNat : 2 * d < q := by exact_mod_cast hq
  have ht : F.IsTorsion := (Scheme.isTorsionAbelianSheaf_characterizations F).1.mp hF
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F
  let R := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K
  let M := (DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj R
  have hpoints (t : Y) :
      IsZero ((upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)).obj M) := by
    let y := Y.algClosurePoint t
    let a := pullback.snd f y
    let i := pullback.fst f y
    have : IsProper a := IsProper.pullback_snd f y
    have hd' := geometricFiber_dimension_le f d hd
      (AlgebraicClosure (Y.residueField t)) y
    have hvan := isZero_higherDirectImage_over_algClosed
      (AlgebraicClosure (Y.residueField t)) a d hd'
      ((upperStar AddCommGrpCat.{u + 1} i).obj F) (isTorsion_upperStar i ht) q hqNat
    have hbc := isIso_baseChange_of_isProper (IsPullback.of_hasPullback f y) K
      (torsionHomology_single F ht)
    rw [baseChange_eq_derivedBaseChangeMapPlus] at hbc
    have := hbc
    exact hvan.of_iso
      (((upperStar AddCommGrpCat.{u + 1} y).mapDerivedCategoryPlusHomologyFunctorIso q).app
          R ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
            (IsPullback.of_hasPullback f y).toCommSq).app K)) ≪≫
        (DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((lowerStar AddCommGrpCat.{u + 1} a).rightDerivedFunctorPlus.mapIso
            (((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlusSingleFunctor 0).app F)))
  have hz := isZero_zero (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
  have : IsIso (hz.from_ M) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun t ↦ Y.algClosurePoint t)
      (fun t ↦ ⟨t, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
      fun t ↦ ?_
    have hz' := Functor.map_isZero (upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)) hz
    exact ⟨⟨hz'.to_ _, (hpoints t).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  exact hz.of_iso (asIso (hz.from_ M))

end AlgebraicGeometry.Etale
