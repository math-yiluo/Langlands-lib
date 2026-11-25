/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkSpecialization
public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.QcqsHigherImagesPrimeTorsion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpecializationCospecializationCompatibility
import WeilConjectures.AlgebraicGeometry.StrictLocalDerivedGlobalExchange
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Proper locally acyclic specialization

## References

* Stacks Project, Tag 0GJW, applied to `G[0]`
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem torsionHomology_single {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    DerivedCategory.Plus.torsionHomology X
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) := by
  intro n
  apply (Scheme.isTorsionSheaf_iff_isTorsion _).2
  by_cases hn : n = 0
  · subst n
    exact hG.of_iso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app G).symm
  · have hZ : IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) :=
      IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)
        ((_root_.DerivedCategory.homologyFunctorFactors _ n).app _)
    exact Scheme.isTorsion_of_nsmul_id_eq_zero (N := 1) (by decide)
      (by simpa using hZ.eq_of_src (𝟙 _) 0)

private theorem isIso_fiberMap_of_proper
    {X Z S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {f : X ⟶ S} [IsProper f] {k : Z ⟶ X} {a : Z ⟶ Spec (.of Ω)}
    {s : Spec (.of Ω) ⟶ S} (sq : IsPullback k a f s)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.torsionHomology X K) :
    IsIso (etaleDerivedFiberMap sq.toCommSq K) := by
  have hbc := isIso_baseChange_of_isProper sq K hK
  rw [baseChange_eq_derivedBaseChangeMapPlus] at hbc
  let := hbc
  let := isIso_globalGerm_identity Ω
  let := isIso_derivedGlobalGerm a (𝟙 (Spec (.of Ω)))
  unfold etaleDerivedFiberMap
  infer_instance

private theorem isIso_strictBaseSheafFiberMap
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (strictBaseSheafFiberMap f G s t) := by
  have sq := (IsPullback.of_hasPullback (strictBaseChangeMap f s) t).paste_horiz
    (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s))
  have := isIso_fiberMap_of_proper sq
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) (torsionHomology_single G hG)
  unfold strictBaseSheafFiberMap strictBaseDerivedFiberMap
  infer_instance

private theorem isIso_closedStrictBaseSheafFiberMap
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    IsIso (closedStrictBaseSheafFiberMap f G s) := by
  have := isIso_strictBaseSheafFiberMap f G hG s
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
  unfold closedStrictBaseSheafFiberMap
  infer_instance

private theorem isIso_strictLocal_restriction
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (f' : X' ⟶ Spec (.of B)) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.torsionHomology X K) :
    IsIso (etaleDerivedRestriction g' K) := by
  have hbc := isIso_baseChange_of_isProper sq K hK
  rw [baseChange_eq_derivedBaseChangeMapPlus] at hbc
  have := hbc
  apply (_root_.DerivedCategory.Plus.isIso_iff _).2
  intro q
  obtain ⟨c₁, c₂, hc⟩ := exists_addEquiv_strictLocal_derivedGlobal_exchange φ f f' g' sq K q
  let e := (_root_.DerivedCategory.Plus.homologyFunctor _ q).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)
  let T := (Scheme.pointSmallEtale
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  have he := ConcreteCategory.bijective_of_isIso (T.map e)
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have hcomp : Function.Bijective (fun x ↦
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).map
        (etaleDerivedRestriction g' K)).hom (c₁ x)) := by
    have h := c₂.bijective.comp he
    convert h using 1
    funext x
    exact (hc x).symm
  exact (Function.Bijective.of_comp_iff _ c₁.bijective).1 hcomp

private theorem torsionHomology_directImage_single
    {X Y : Scheme.{u}} (h : X ⟶ Y) [QuasiCompact h] [QuasiSeparated h]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    DerivedCategory.Plus.torsionHomology Y
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) := by
  intro n
  apply (Scheme.isTorsionSheaf_iff_isTorsion _).2
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    apply (Scheme.isTorsionAbelianSheaf_characterizations _).1.mp
    apply (Scheme.isTorsionAbelianSheaf_characterizations _).2.mpr
    intro Ω _ _ s x
    obtain ⟨m, hm, hmx, -⟩ := qcqs_higherDirectImages_prime_torsion h Set.univ G
      (fun Ω _ _ s x ↦ by
        obtain ⟨m, hm, hmx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
          ((Scheme.isTorsion_iff_isAddTorsion_sheafFiber G).mp hG Ω s x)
        exact ⟨m, hm, hmx, fun _ _ _ ↦ Set.mem_univ _⟩) q Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, hmx⟩
  · have hz : IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
      Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar AddCommGrpCat.{u + 1} h)
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) 0 (lt_of_not_ge hn)
    exact Scheme.isTorsion_of_nsmul_id_eq_zero (N := 1) (by decide)
      (by
        simpa only [one_smul] using hz.eq_of_src (𝟙 _) 0)

private theorem local_pointEvaluation
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) [IsLocalRing (Scheme.strictHenselizationRing s)] :
    IsLocalHom (Scheme.strictHenselizationRingPointEvaluation s) := by
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  let ψ := Scheme.strictHenselizationPointEvaluationToSep s rfl
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    (Scheme.strictHenselizationPointEvaluationToSep_surjective s rfl)
  let ι := (IntermediateField.val
    (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom
  have : IsLocalHom (Scheme.smallStrictHenselizationColimitIso s).hom.hom :=
    isLocalHom_of_isIso _
  exact (inferInstance :
    IsLocalHom ((ι.comp ψ).comp (Scheme.smallStrictHenselizationColimitIso s).hom.hom))

private theorem isIso_cospecialization_of_proper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : G.IsTorsion) (hf : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (etaleCospecialization f G hf s t) := by
  obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure s
  let := hlocal
  let := hstrict
  have := local_pointEvaluation s
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let i := strictBaseFiberInclusion f s
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := strictBaseFiberInclusion f s t
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} p).obj G)
  let K' := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
    ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K)
  have ht : DerivedCategory.Plus.torsionHomology _ K' := by
    let e := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).mapIso
      (((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlusSingleFunctor 0).app
        ((upperStar AddCommGrpCat.{u + 1} p).obj G))
    have htor := torsionHomology_directImage_single h _
      (isTorsion_upperStar h (isTorsion_upperStar p hG))
    intro n
    have := htor n
    exact @Scheme.IsTorsionSheaf.of_iso _ _ _
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).mapIso e.symm) (htor n)
  have : IsAlgClosed (IsLocalRing.ResidueField Ω) :=
    IsAlgClosed.of_ringEquiv Ω (IsLocalRing.ResidueField Ω)
      (RingEquiv.ofBijective (IsLocalRing.residue Ω)
      ⟨(IsLocalRing.residue Ω).injective, IsLocalRing.residue_surjective⟩)
  have hr := isIso_strictLocal_restriction (Scheme.strictHenselizationRingPointEvaluation s)
    (strictBaseChangeMap f s)
    (pullback.snd (strictBaseChangeMap f s)
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s))))
    i (IsPullback.of_hasPullback _ _) K' ht
  have := hr
  have := isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative f G hf s t
  unfold etaleCospecialization
  infer_instance

private theorem exact_nt_homology
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F ⟶ G) (K : _root_.DerivedCategory.Plus C)
    [IsIso ((Functor.rightDerivedFunctorPlusNatTrans τ).app K)] (q : ℤ) :
    IsIso (τ.app ((_root_.DerivedCategory.Plus.homologyFunctor C q).obj K)) := by
  let M := _root_.DerivedCategory.Plus.Qh.objPreimage K
  have e : _root_.DerivedCategory.Plus.Qh.obj M ≅ K :=
    _root_.DerivedCategory.Plus.Qh.objObjPreimageIso K
  have hτ : IsIso ((Functor.rightDerivedFunctorPlusNatTrans τ).app
      (_root_.DerivedCategory.Plus.Qh.obj M)) :=
    (NatTrans.isIso_app_iff_of_iso _ e).2 inferInstance
  have : IsIso F.rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit F
  have : IsIso G.rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit G
  have : IsIso (G.rightDerivedFunctorPlusUnith.app M) :=
    NatIso.isIso_app_of_isIso G.rightDerivedFunctorPlusUnith M
  have : IsIso (F.rightDerivedFunctorPlusUnith.app M) :=
    NatIso.isIso_app_of_isIso F.rightDerivedFunctorPlusUnith M
  have he := Functor.rightDerivedFunctorPlusNatTrans_app τ M
  have hi : IsIso (_root_.DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus τ).app M)) := by
    have : IsIso (_root_.DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus τ).app M) ≫
          G.rightDerivedFunctorPlusUnith.app M) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.rightDerivedFunctorPlusUnith.app M)
  rcases M with ⟨M, hM⟩
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
  have hia : IsIso (HomologicalComplex.homologyMap a q) := by
    have hiq := Functor.map_isIso (_root_.DerivedCategory.Plus.homologyFunctor D q)
      (_root_.DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus τ).app
        ⟨(HomotopyCategory.quotient _ _).obj L, hM⟩))
    change IsIso ((_root_.DerivedCategory.homologyFunctor D q).map
      (_root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map a))) at hiq
    have hiq' := (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (_root_.DerivedCategory.quotientCompQhIso D)
        (_root_.DerivedCategory.homologyFunctor D q)) a).1 hiq
    exact (NatIso.isIso_map_iff (_root_.DerivedCategory.homologyFunctorFactors D q) a).1 hiq'
  have hτL : IsIso (τ.app (L.homology q)) := by
    change IsIso (τ.app (L.sc q).homology)
    rw [NatTrans.app_homology τ (L.sc q)]
    change IsIso (_ ≫ HomologicalComplex.homologyMap a q ≫ _)
    infer_instance
  let eh : (_root_.DerivedCategory.Plus.homologyFunctor C q).obj K ≅ L.homology q :=
    (_root_.DerivedCategory.Plus.homologyFunctor C q).mapIso e.symm ≪≫
      (_root_.DerivedCategory.homologyFunctor C q).mapIso
        ((_root_.DerivedCategory.quotientCompQhIso C).app L) ≪≫
      (_root_.DerivedCategory.homologyFunctorFactors C q).app L
  exact (NatTrans.isIso_app_iff_of_iso τ eh).2 hτL

/-- Proper local acyclicity makes specialization on every higher direct-image stalk
invertible for torsion abelian coefficients, without any common annihilator or finite-stalk
hypothesis. -/
theorem isIso_etaleStalkSpecialization_of_proper_locallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : G.IsTorsion) (hf : IsLocallyAcyclicRelative f G)
    (q : ℕ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso (etaleStalkSpecialization s t
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by
  let K := (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have := isIso_strictBaseSheafFiberMap f G hG s t
  have := isIso_closedStrictBaseSheafFiberMap f G hG s
  have := isIso_cospecialization_of_proper f G hG hf s t
  have hsp : IsIso ((derivedEtaleStalkSpecialization s t).app K) := by
    have : IsIso ((derivedEtaleStalkSpecialization s t).app K ≫
        strictBaseSheafFiberMap f G s t ≫ etaleCospecialization f G hf s t) := by
      rw [specialization_cospecialization_compatibility f G hf s t]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (strictBaseSheafFiberMap f G s t ≫ etaleCospecialization f G hf s t)
  let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let T := (Scheme.pointSmallEtale
    (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber
    (A := AddCommGrpCat.{u + 1})
  let τ := etaleStalkSpecializationNatTrans s t
  have hτ : IsIso ((Functor.rightDerivedFunctorPlusNatTrans τ).app K) := by
    have hcomp : IsIso (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K ≫
        (Functor.rightDerivedFunctorPlusNatTrans τ).app K ≫
          T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K) := hsp
    have : IsIso ((F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K ≫
        (Functor.rightDerivedFunctorPlusNatTrans τ).app K) ≫
          T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K) := by
      simpa only [Category.assoc] using hcomp
    have : IsIso (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K ≫
        (Functor.rightDerivedFunctorPlusNatTrans τ).app K) :=
      IsIso.of_isIso_comp_right _
        (T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K)
    exact IsIso.of_isIso_comp_left
      (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K) _
  exact exact_nt_homology τ K (q : ℤ)

end AlgebraicGeometry.Etale
