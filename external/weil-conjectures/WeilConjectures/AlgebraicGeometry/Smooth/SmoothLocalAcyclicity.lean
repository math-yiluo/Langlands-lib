/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeStrictLocalCohomology
import WeilConjectures.AlgebraicGeometry.Strict.StrictBaseClosedPointLocalizations
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalConstantComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.ProperBaseChange.StrictlyHenselianEtaleAcyclic
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-!
# Smooth morphisms are universally locally acyclic

Source: Stacks Project, Tag 0GJQ, proposition-smooth-locally-acyclic
(blueprint: lem-weil-pbc-smooth-local-acyclicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

private def ConstantAcyclic (Z : Scheme.{u}) (M : AddCommGrpCat.{u + 1}) : Prop :=
  IsIso ((constantSheafΓAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app M) ∧
    ∀ q : ℕ, 0 < q → Limits.IsZero
      ((cohomology AddCommGrpCat.{u + 1} Z (q : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)))

private theorem constantSection_pullback
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) (N : AddCommGrpCat.{u + 1}) :
    (constantSheafΓAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app N ≫
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N) ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app N) =
      (constantSheafΓAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app N := by
  let adjY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} Limits.terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1} Limits.terminalIsTerminal
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let e := lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g
  apply (cancel_mono ((Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} Limits.terminalIsTerminal).hom.app _)).1
  simp only [Category.assoc]
  rw [(Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
    AddCommGrpCat.{u + 1} Limits.terminalIsTerminal).hom.naturality]
  simp only [globalSectionsUpperStarMap, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Sheaf.ΓNatIsoSheafSections]
  have hY := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}) adjY N
  have hZ := Adjunction.unit_rightAdjointUniq_hom_app
    (constantSheafΓAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}) adjZ N
  simp only [← Category.assoc]
  rw [hY, hZ]
  exact Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ N

private theorem constantAcyclic_pullback
    {Y Z : Scheme.{u}} (p : Y ⟶ Z) (M : AddCommGrpCat.{u + 1})
    (hZ : ConstantAcyclic Z M)
    (hp : ∀ q : ℕ, Function.Bijective (cohomologyMap p
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q)) :
    ConstantAcyclic Y M := by
  let F := (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} p).app M
  have hu := hZ.1
  have hmap := (bijective_cohomologyMap_zero_iff p F).mp (hp 0)
  constructor
  · rw [← constantSection_pullback p M]
    infer_instance
  · intro q hq
    obtain ⟨a⟩ := Scheme.nonempty_sheafH_extDerivedIso Z q
    obtain ⟨b⟩ := Scheme.nonempty_sheafH_extDerivedIso Y q
    have hz : Limits.IsZero ((Sheaf.functorH.{u + 1} Z.smallEtaleTopology q).obj F) :=
      (hZ.2 q hq).of_iso (a.app F)
    have hs : Subsingleton (Sheaf.H.{u + 1} F q) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp hz
    have ht : Subsingleton (Sheaf.H.{u + 1} ((upperStar AddCommGrpCat.{u + 1} p).obj F) q) :=
      Function.Surjective.subsingleton (hp q).2
    have ht' : Limits.IsZero ((Sheaf.functorH.{u + 1} Y.smallEtaleTopology q).obj
        ((upperStar AddCommGrpCat.{u + 1} p).obj F)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr ht
    let H := DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)
    exact (ht'.of_iso (b.app _).symm).of_iso (H.mapIso e).symm

private theorem constantAcyclic_strictlyHenselian
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    (M : AddCommGrpCat.{u + 1}) : ConstantAcyclic (Spec (.of R)) M := by
  let J := (Spec (.of R)).smallEtaleTopology
  let adj := constantSheafΓAdj J AddCommGrpCat.{u + 1}
  let adj' := constantSheafAdj J AddCommGrpCat.{u + 1} (Scheme.isTerminalEtaleTerminal R)
  have hu : IsIso (adj'.unit.app M) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (Scheme.bijective_toSheafify_app_of_isStrictlyHenselianLocalRing R
        ((Functor.const _).obj M))
  constructor
  · have hh := Adjunction.unit_rightAdjointUniq_hom_app adj adj' M
    exact (isIso_comp_right_iff _ _).mp (hh.symm ▸ hu)
  · intro q hq
    exact (strictlyHenselian_etale_acyclic R inferInstance).2 _ _ (by omega)

private noncomputable def constantStalkIso
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (M : AddCommGrpCat.{u + 1}) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ≅ M := by
  let Φ := Scheme.pointSmallEtale x
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  exact (Φ.uliftSheafFiberIso AddCommGrpCat.{u + 1}).symm.app _ ≪≫
    (Φ.ulift.{u + 1}).sheafFiberConstantSheafIso M

private theorem smooth_abelian_exchange
    {X S T : Scheme.{u}} (f : X ⟶ S) [Smooth f] (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤)))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
      (m : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F), n • m = 0) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback f g).toCommSq.flip).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let U := sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let G := U.objPreimage F
  let eF : U.obj G ≅ F := U.objObjPreimageIso F
  have : Scheme.IsTorsionSheafOfInvertibleOrder S G := by
    constructor
    intro Ω _ _ s x
    let Φ := Scheme.pointSmallEtale s
    let V := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
    have : LocallySmall.{u + 1} T.Etale :=
      @locallySmall_of_univLE T.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
    let φ := (Φ.uliftSheafFiberIso AddCommGrpCat.{u + 1}).symm.app (U.obj G) ≪≫
      ((Φ.ulift.{u + 1}).sheafFiberCompIso V).app G ≪≫
      V.mapIso ((Φ.uliftSheafFiberIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).app G)
    let e := φ.symm ≪≫ Φ.sheafFiber.mapIso eF
    refine ⟨n, hn, hu, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    change e.hom.hom (n • x) = e.hom.hom 0
    simpa only [map_nsmul, map_zero] using hF Ω s (e.hom.hom x)
  let sq := (IsPullback.of_hasPullback f g).flip
  let τ := derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  apply (NatTrans.isIso_app_iff_of_iso τ
    ((DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)).1
  apply (NatTrans.isIso_app_iff_of_iso τ
    ((U.mapDerivedCategoryPlusSingleFunctor 0).app G)).1
  apply (isIso_derivedBaseChangeMapPlus_app_forget₂_iff sq.toCommSq
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)).2
  rw [← baseChange_eq_derivedBaseChangeMapPlus]
  exact isIso_baseChange_app_singleFunctor_obj_of_smooth _ f sq G

private theorem strictMap_structural
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    localAcyclicityStrictMap f x ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f :=
  (existsUnique_localAcyclicityStrictMap f x).choose_spec.1.1

private theorem strictMap_point
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation x)) ≫
        localAcyclicityStrictMap f x =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation (x ≫ f))) :=
  (existsUnique_localAcyclicityStrictMap f x).choose_spec.1.2

private theorem cohomology_pullback_iso
    {Y Z : Scheme.{u}} (p : Y ⟶ Z)
    {F G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (q : ℕ) (h : Function.Bijective (cohomologyMap p F q)) :
    Function.Bijective (cohomologyMap p G q) := by
  have hh : ⇑(cohomologyMap p G q) =
      Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} p).mapIso e).hom q ∘
        cohomologyMap p F q ∘ Sheaf.H.map e.inv q := by
    ext x
    simp only [Function.comp_apply, Functor.mapIso_hom, ← cohomologyMap_map,
      ← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  rw [hh]
  exact (ConcreteCategory.bijective_of_isIso
    ((Sheaf.functorH.{u + 1} Y.smallEtaleTopology q).map
      ((upperStar AddCommGrpCat.{u + 1} p).mapIso e).hom)).comp
    (h.comp (ConcreteCategory.bijective_of_isIso
      ((Sheaf.functorH.{u + 1} Z.smallEtaleTopology q).map e.inv)))

private theorem smooth_strict_base_constantAcyclic
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    [IsIso (Scheme.strictHenselizationStructuralMap (x ≫ f))]
    {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S)
    (M : AddCommGrpCat.{u + 1}) (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) (hM : ∀ m : M, n • m = 0) :
    ConstantAcyclic (Limits.pullback (Scheme.strictHenselizationStructuralMap x ≫ f) t) M := by
  let F := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  have : QuasiCompact t := inferInstance
  have : QuasiSeparated t := inferInstance
  have hF (L : Type u) [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ Spec (.of K))
      (m : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) : n • m = 0 := by
    let e := constantStalkIso s M
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    change e.hom.hom (n • m) = e.hom.hom 0
    simpa only [map_nsmul, map_zero] using hM (e.hom.hom m)
  have hex := smooth_abelian_exchange f t F n hn hu hF
  let A := Scheme.strictHenselizationScheme (x ≫ f)
  let B := Scheme.strictHenselizationScheme x
  let i := Scheme.strictHenselizationStructuralMap (x ≫ f)
  let j := Scheme.strictHenselizationStructuralMap x
  let d := localAcyclicityStrictMap f x
  let a := Spec.preimage d
  have ha : Spec.map a = d := Spec.map_preimage d
  have he : Scheme.strictHenselizationRingPointEvaluation (x ≫ f) =
      (Scheme.strictHenselizationRingPointEvaluation x).comp a.hom := by
    have hh : Spec.map (CommRingCat.ofHom
        ((Scheme.strictHenselizationRingPointEvaluation x).comp a.hom)) =
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation (x ≫ f))) := by
      simp only [CommRingCat.ofHom_comp, Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation x)) ≫
        Spec.map a = _
      rw [ha]
      exact strictMap_point f x
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective hh)).symm
  have hastruct : Spec.map a ≫ i = j ≫ f := by
    rw [ha]
    exact strictMap_structural f x
  let p := Limits.pullback.map (j ≫ f) t i t (Spec.map a) (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans hastruct.symm)
    ((Category.comp_id t).trans (Category.id_comp t).symm)
  have hbij (q : ℕ) : Function.Bijective
      (cohomologyMap p ((upperStar AddCommGrpCat.{u + 1} (Limits.pullback.snd i t)).obj F) q) := by
    exact (isIso_exchange_iff_strictLocalCohomology f t F q).mp
      (by infer_instance) Ω x a he hastruct
  have hK : IsStrictlyHenselianLocalRing K :=
    ⟨IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (IsLocalRing.residue K)
      ⟨(IsLocalRing.residue K).injective, IsLocalRing.residue_surjective⟩)⟩
  let := hK
  have hE : ConstantAcyclic (Limits.pullback i t) M :=
    constantAcyclic_pullback (Limits.pullback.snd i t) M (constantAcyclic_strictlyHenselian K M)
      (fun q ↦ cohomologyMap_bijective _ _ _)
  apply constantAcyclic_pullback p M hE
  intro q
  exact cohomology_pullback_iso p
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
      (Limits.pullback.snd i t)).app M) q (hbij q)

private theorem strict_congr_structural
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {x y : Spec (.of Ω) ⟶ S} (h : x = y) :
    eqToHom (congrArg Scheme.strictHenselizationScheme h) ≫
        Scheme.strictHenselizationStructuralMap y =
      Scheme.strictHenselizationStructuralMap x := by
  subst y
  simp

private theorem strict_congr_point
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {x y : Spec (.of Ω) ⟶ S} (h : x = y) :
    Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation x)) ≫
        eqToHom (congrArg Scheme.strictHenselizationScheme h) =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation y)) := by
  subst y
  simp

private theorem strict_base_fibre_constantAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {X' : Scheme.{u}} (p : X' ⟶ X)
    (f' : X' ⟶ Scheme.strictHenselizationScheme s) [Smooth f']
    (hcart : IsPullback p f' f (Scheme.strictHenselizationStructuralMap s))
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (x' : Spec (.of Ξ) ⟶ X')
    (a : Spec (.of Ξ) ⟶ Spec (.of Ω))
    (hclosed : x' ≫ f' =
      a ≫ Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
    {K : Type u} [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Scheme.strictHenselizationScheme ((x' ≫ p) ≫ f))
    (M : AddCommGrpCat.{u + 1}) (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(Scheme.strictHenselizationScheme s, ⊤)))
    (hM : ∀ m : M, n • m = 0) : ConstantAcyclic (localAcyclicityFiber f (x' ≫ p) t) M := by
  have hpoint : (x' ≫ f') ≫ Scheme.strictHenselizationStructuralMap s =
      (x' ≫ p) ≫ f := by
    simpa only [Category.assoc] using congrArg (fun m ↦ x' ≫ m) hcart.w.symm
  let b := localAcyclicityStrictMap (Scheme.strictHenselizationStructuralMap s) (x' ≫ f') ≫
    eqToHom (congrArg Scheme.strictHenselizationScheme hpoint)
  have hb : b ≫ Scheme.strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      Scheme.strictHenselizationStructuralMap (x' ≫ f') ≫
        Scheme.strictHenselizationStructuralMap s := by
    dsimp only [b]
    rw [Category.assoc, strict_congr_structural hpoint, strictMap_structural]
  have hbpoint : Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationRingPointEvaluation (x' ≫ f'))) ≫ b =
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation
        ((x' ≫ p) ≫ f))) := by
    dsimp only [b]
    rw [← Category.assoc, strictMap_point, strict_congr_point hpoint]
  obtain ⟨hi, _, e, _, _, hE⟩ := Scheme.strictBaseClosedPointLocalizations f s p f' hcart
    x' a hclosed b hb hbpoint (localAcyclicityStrictMap f (x' ≫ p))
    (strictMap_structural f (x' ≫ p)) (strictMap_point f (x' ≫ p))
    (localAcyclicityStrictMap p x') (strictMap_structural p x') (strictMap_point p x')
  have : IsAffine (Scheme.strictHenselizationScheme s) := by
    unfold Scheme.strictHenselizationScheme
    infer_instance
  have := hi
  obtain ⟨E, _, _⟩ := hE K (t ≫ e.inv)
  have hz := smooth_strict_base_constantAcyclic f' x' (t ≫ e.inv) M n hn hu hM
  have hh : ConstantAcyclic (Limits.pullback (localAcyclicityStrictMap f (x' ≫ p))
      ((t ≫ e.inv) ≫ e.hom)) M :=
    constantAcyclic_pullback E.inv M hz (fun q ↦ cohomologyMap_bijective _ _ _)
  simpa only [localAcyclicityFiber, Category.assoc, e.inv_hom_id,
    Category.comp_id] using hh

private theorem constantAcyclic_of_iso
    (Z : Scheme.{u}) {M N : AddCommGrpCat.{u + 1}} (e : M ≅ N)
    (hM : ConstantAcyclic Z M) : ConstantAcyclic Z N := by
  let C := constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ := Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}
  let η := (constantSheafΓAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}).unit
  have hu := hM.1
  constructor
  · have hh : η.app N = e.inv ≫ η.app M ≫ (C ⋙ Γ).map e.hom := by
      rw [← η.naturality e.hom]
      simp
    rw [hh]
    infer_instance
  · intro q hq
    let H := DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} Z (q : ℤ)
    exact (hM.2 q hq).of_iso ((C ⋙ H).mapIso e).symm

private theorem admissible_isUnit_strict_base
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (n : ℕ) (hn : 0 < n)
    (hp : ringChar (X.residueField (x default)) = 0 ∨
      n.Coprime (ringChar (X.residueField (x default)))) :
    IsUnit (n : Γ(Scheme.strictHenselizationScheme (x ≫ f), ⊤)) := by
  let κ := X.residueField (x default)
  have hκ : IsUnit (n : κ) := by
    rcases hp with hp | hp
    · have : CharZero κ := (CharP.ringChar_zero_iff_CharZero κ).mp hp
      exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
    · let := invertibleOfCoprime (R := κ) hp
      exact isUnit_of_invertible _
  have hx : x (IsLocalRing.closedPoint Ω) = x default :=
    congrArg x (Subsingleton.elim _ _)
  have hκ' : IsUnit (n : X.residueField (x (IsLocalRing.closedPoint Ω))) := by
    simpa only [map_natCast] using hκ.map (X.residueFieldCongr hx).inv.hom
  have hΩ : IsUnit (n : Ω) := by
    simpa only [map_natCast] using
      hκ'.map (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom
  let s := x ≫ f
  let R := Scheme.strictHenselizationRing s
  obtain ⟨hl, _⟩ := strictHenselizationLocalStructure s
  let := hl
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  let ψ := Scheme.strictHenselizationPointEvaluationToSep s rfl
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    (Scheme.strictHenselizationPointEvaluationToSep_surjective s rfl)
  let ι := (IntermediateField.val
    (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom
  have : IsLocalHom (Scheme.smallStrictHenselizationColimitIso s).hom.hom :=
    isLocalHom_of_isIso _
  have : IsLocalHom (Scheme.strictHenselizationRingPointEvaluation s) := by
    change IsLocalHom ((ι.comp ψ).comp (Scheme.smallStrictHenselizationColimitIso s).hom.hom)
    infer_instance
  have hR : IsUnit (n : R) :=
    isUnit_of_map_unit (Scheme.strictHenselizationRingPointEvaluation s) _ (by
      simpa only [map_natCast] using hΩ)
  simpa only [map_natCast] using hR.map (Scheme.ΓSpecIso (.of R)).inv.hom

private theorem constantAcyclic_point_congr
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {x y : Spec (.of Ω) ⟶ X} (h : x = y)
    {K : Type u} [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Scheme.strictHenselizationScheme (y ≫ f))
    (M : AddCommGrpCat.{u + 1}) :
    ConstantAcyclic (localAcyclicityFiber f x
      (t ≫ eqToHom (congrArg (fun z ↦ Scheme.strictHenselizationScheme (z ≫ f)) h.symm))) M →
      ConstantAcyclic (localAcyclicityFiber f y t) M := by
  subst y
  intro hh
  simpa only [eqToHom_refl, Category.comp_id] using hh

private theorem smooth_isLocallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] : IsLocallyAcyclic f := by
  intro Ω _ _ x n hn hp K _ _ t
  let M := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  let G := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let s := x ≫ f
  let A := Scheme.strictHenselizationScheme s
  let i := Scheme.strictHenselizationStructuralMap s
  let z := Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s))
  let p : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
  let f' : Limits.pullback f i ⟶ A := Limits.pullback.snd f i
  let x' : Spec (.of Ω) ⟶ Limits.pullback f i :=
    Limits.pullback.lift x z (Scheme.strictHenselizationClosedLift_over s).symm
  have hxp : x' ≫ p = x := Limits.pullback.lift_fst _ _ _
  have hxz : x' ≫ f' = (𝟙 _) ≫ z := by simp [x', f']
  have hM (m : M) : n • m = 0 := by
    apply ULift.ext
    change n • m.down = 0
    simp [nsmul_eq_mul]
  have hz : ConstantAcyclic (localAcyclicityFiber f x t) M := by
    let ht : Spec (.of K) ⟶ Scheme.strictHenselizationScheme ((x' ≫ p) ≫ f) :=
      t ≫ eqToHom (congrArg (fun y ↦ Scheme.strictHenselizationScheme (y ≫ f)) hxp.symm)
    have hh := strict_base_fibre_constantAcyclic f s p f'
      (IsPullback.of_hasPullback f i) x' (𝟙 _) hxz ht M n hn
      (admissible_isUnit_strict_base f x n hn hp) hM
    exact constantAcyclic_point_congr f hxp t M hh
  have hconst : G.IsConstant X.smallEtaleTopology := ⟨M, ⟨Iso.refl _⟩⟩
  have : Scheme.IsLocallyConstantSheaf G := hconst.isLocallyConstantSheaf
  obtain ⟨e, he⟩ := exists_strictLocalConstantComparison f x t G
  have hstalk := constantAcyclic_of_iso (localAcyclicityFiber f x t)
    (constantStalkIso x M).symm hz
  have hu := hstalk.1
  constructor
  · rw [he]
    infer_instance
  · intro q hq
    let H := DerivedCategory.singleFunctor _ 0 ⋙
      cohomology AddCommGrpCat.{u + 1} (localAcyclicityFiber f x t) (q : ℤ)
    exact (hstalk.2 q hq).of_iso (H.mapIso e).symm

/-- Smooth morphisms are universally locally acyclic, and in particular locally acyclic.
There is no properness or relative-dimension hypothesis.
Source: Stacks Project, Tag 0GJQ, proposition-smooth-locally-acyclic
(blueprint: lem-weil-pbc-smooth-local-acyclicity).

Proof:
1. Smoothness is stable under arbitrary base change, so it suffices to prove local
acyclicity. Fix a geometric point x and a positive integer n prime to its residue
characteristic. Then n is a unit in its geometric field.
2. Replace the base by its strict localization at f(x). Its evaluation into the
geometric field is local, so n is invertible on this affine strict-local base. Lift x
to the base-changed scheme. The pointed strict-local comparison identifies the original
vanishing-cycle fibres with those for this base change
(`lem-weil-pbc-strict-base-closed-point-localizations`).
3. Apply smooth base change to each geometric test point of this base, with constant
coefficients Z/n. Transfer the exchange isomorphism from integer-module sheaves to
abelian sheaves. The strict-local exchange criterion gives bijective cohomology pullbacks
from the test field to the strict-local fibre
(`lem-weil-pbc-exchange-strict-local-cohomology`).
4. The separably closed test field is strictly henselian. Its constant-section unit is
invertible and its positive cohomology vanishes. Transfer these properties along the
comparison maps, using the degree-zero comparison, the Ext/derived-cohomology comparison,
and the inverse-image constant-sheaf isomorphism. The adjunction identity for constant
sections ensures this identifies the actual constant-section unit.
5. The strict-local constant comparison identifies the canonical alpha with that unit
followed by the coefficient isomorphism
(`lem-weil-pbc-strict-local-constant-comparison`). Transport along the constant-stalk
isomorphism gives the required invertibility and positive cohomology vanishing.
All test points and n were arbitrary; step 1 gives universality. -/
theorem smooth_localAcyclicity {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    IsUniversallyLocallyAcyclic f ∧ IsLocallyAcyclic f := by
  exact ⟨fun _ _ ↦ smooth_isLocallyAcyclic _, smooth_isLocallyAcyclic f⟩

end AlgebraicGeometry.Etale
