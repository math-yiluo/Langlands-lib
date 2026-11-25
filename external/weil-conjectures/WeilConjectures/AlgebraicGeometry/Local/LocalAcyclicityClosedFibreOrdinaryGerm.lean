/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityStrictFibreComparison
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalOrdinaryDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.GlobalSectionsIsoOverTransport
import WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionConeStalkIso
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationRingResidue
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The unit map on closed-fibre stalks

## References

* Stacks Project, Tag 0GJU, ordinary germ calculation
* Tag 0GJP
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

private noncomputable def restriction {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G)

private theorem restriction_spec {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (strictLocalSectionCone s).IsRestriction G (restriction s G) :=
  (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction G)).1

private theorem restriction_isIso {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (restriction s G) := by
  classical
  let r := restriction s G
  have hr := restriction_spec s G
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
    strictHenselizationRingResidue s rfl
  let := hlocal
  let y := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
  have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
    rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  refine (strictLocalSectionCone s).isIso_restriction y hbase ?_
    G ((Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 _) r hr
  intro i
  let n := (equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj i
  change y ≫ (strictLocalNeighbourhoodSection s i).left ≫
    pullback.fst ((Scheme.AffineEtale.Spec S).obj n.1).hom
      (Scheme.strictHenselizationStructuralMap s) = n.2.left
  dsimp only [n]
  simp only [strictLocalNeighbourhoodSection,
    MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk]
  erw [pullback.lift_fst]
  simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using! hpoint i

attribute [local irreducible] strictLocalSectionCone upperStar upperStarLowerStarAdjunction

private theorem naturality_three {C : Type*} [Category C]
    {A B D E H J L M : C}
    (a : A ⟶ B) (b : D ⟶ E) (c : H ⟶ J) (d : L ⟶ M)
    (l : A ⟶ D) (l' : B ⟶ E) (m : D ⟶ H) (m' : E ⟶ J)
    (n : H ⟶ L) (n' : J ⟶ M)
    (h₁ : a ≫ l' = l ≫ b) (h₂ : b ≫ m' = m ≫ c)
    (h₃ : c ≫ n' = n ≫ d) :
    a ≫ l' ≫ m' ≫ n' = l ≫ m ≫ n ≫ d := by
  rw [← Category.assoc a, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc b, h₂]
  simp only [Category.assoc]
  rw [h₃]

private theorem cone_restriction_naturality
    {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {I : Type u} [Category.{u} I]
    {N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements} {g : T ⟶ S}
    (c : PointedEtaleSectionCone g N)
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : F ⟶ G)
    (rF : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj F))
    (rG : (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (hrF : c.IsRestriction F rF) (hrG : c.IsRestriction G rG) :
    (Scheme.pointSmallEtale s).sheafFiber.map a ≫ rG =
      rF ≫ (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStar AddCommGrpCat.{u + 1} g).map a) := by
  have : N.Initial := c.initial
  let d := ((Scheme.pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
  let hd : IsColimit d :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
  apply hd.hom_ext
  intro j
  change (Scheme.pointSmallEtale s).toPresheafFiber
      (N.obj j.unop).1 (N.obj j.unop).2 F.obj ≫ _ = _
  erw [← Category.assoc,
    (Scheme.pointSmallEtale s).toPresheafFiber_naturality a.hom, Category.assoc]
  erw [hrG j.unop]
  have hrF' := hrF j.unop
  conv_rhs => erw [← Category.assoc, hrF']
  dsimp only [PointedEtaleSectionCone.restriction]
  have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality a
  have he := congrArg (fun b ↦ b.hom.app (Opposite.op (N.obj j.unop).1)) hu
  dsimp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at he
  have hn := ((upperStar AddCommGrpCat.{u + 1} g).map a).hom.naturality
    (c.section_ j.unop).op
  erw [Category.assoc, Category.assoc]
  refine naturality_three _ _ _ _ _ _ _ _ _ _ he hn.symm ?_
  exact NatTrans.naturality
    (C := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (D := AddCommGrpCat.{u + 1}) _ ((upperStar AddCommGrpCat.{u + 1} g).map a)

private theorem restriction_naturality {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
    (Scheme.pointSmallEtale s).sheafFiber.map a ≫ restriction s G =
      restriction s F ≫
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{u + 1}).map
          ((upperStar AddCommGrpCat.{u + 1}
            (Scheme.strictHenselizationStructuralMap s)).map a) := by
  exact cone_restriction_naturality (strictLocalSectionCone s) a
    (restriction s F) (restriction s G) (restriction_spec s F) (restriction_spec s G)

private theorem globalSectionsUpperStarMap_eq
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g F =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F) ≫
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g).hom.app _ := by
  let e := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  change _ = _ ≫ e.hom.app _ ≫ _ ≫ _
  rw [e.hom.naturality_assoc]
  rfl

private theorem comparison_chain {C : Type*} [Category C]
    {A B D E H J L M N P : C}
    (a : A ⟶ B) (c₁ : A ⟶ D) (c₂ : B ⟶ E) (n : D ⟶ E)
    (r₁ : D ⟶ H) (r₂ : E ⟶ J) (η : H ⟶ J) (b : J ⟶ L)
    (w : H ⟶ M) (s : M ⟶ L) (V : L ≅ P) (U : H ≅ N)
    (r : N ⟶ P) {Q : C} (R : Q ⟶ N) [IsIso R]
    (hc : a ≫ c₂ = c₁ ≫ n) (hr : n ≫ r₂ = r₁ ≫ η)
    (hu : η ≫ b = w ≫ s) (ht : w ≫ s ≫ V.hom = U.hom ≫ r) :
    a ≫ c₂ ≫ r₂ ≫ b ≫ V.hom =
      (c₁ ≫ r₁ ≫ U.hom ≫ inv R) ≫ (R ≫ r) := by
  rw [← Category.assoc a, hc]
  simp only [Category.assoc]
  rw [← Category.assoc n, hr]
  simp only [Category.assoc]
  rw [← Category.assoc η, hu]
  simp only [Category.assoc]
  rw [ht]
  simp only [IsIso.inv_hom_id_assoc]

private theorem alpha_eq {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    localAcyclicityAlpha f x t G = restriction x G ≫
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1}
        (pullback.fst (localAcyclicityStrictMap f x) t)
        ((upperStar AddCommGrpCat.{u + 1}
          (Scheme.strictHenselizationStructuralMap x)).obj G) ≫
      (Sheaf.Γ (localAcyclicityFiber f x t).smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarComp AddCommGrpCat.{u + 1}
          (pullback.fst (localAcyclicityStrictMap f x) t)
          (Scheme.strictHenselizationStructuralMap x)).inv.app G)) := rfl

attribute [local irreducible] restriction localAcyclicityStrictMap
attribute [local irreducible] squareUpperStarIso upperStarComp baseChangeMap
attribute [local irreducible] Sheaf.Γ upperStarCompSheafFiberIso localAcyclicityAlpha

/-- The ordinary adjunction unit on a closed-fibre stalk is the local-acyclicity map. -/
theorem closedFibre_unit_stalk_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (z : Spec (.of Ξ) ⟶
      pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
        (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))) :
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
    let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationRingPointEvaluation s)))
    let h := pullback.fst f' t
    let x := (z ≫ i) ≫ p
    let K := (upperStar AddCommGrpCat.{u + 1} p).obj G
    let β := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app K
    let a := (Scheme.pointSmallEtale z).sheafFiber.map
      ((upperStar AddCommGrpCat.{u + 1} i).map β)
    ∃ e : Scheme.strictHenselizationScheme s ≅ Scheme.strictHenselizationScheme (x ≫ f),
      ∃ A : (Scheme.pointSmallEtale z).sheafFiber.obj
          ((upperStar AddCommGrpCat.{u + 1} i).obj K) ≅
          (Scheme.pointSmallEtale x).sheafFiber.obj G,
        ∃ B : (Scheme.pointSmallEtale z).sheafFiber.obj
            ((upperStar AddCommGrpCat.{u + 1} i).obj
              (((upperStar AddCommGrpCat.{u + 1} h) ⋙
                (lowerStar AddCommGrpCat.{u + 1} h)).obj K)) ≅
            (Sheaf.Γ (localAcyclicityFiber f x (t ≫ e.hom)).smallEtaleTopology
              AddCommGrpCat.{u + 1}).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
                  Scheme.strictHenselizationStructuralMap x)).obj G),
          a ≫ B.hom = A.hom ≫ localAcyclicityAlpha f x (t ≫ e.hom) G := by
  dsimp only
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
  let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
    (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := pullback.fst f' t
  let x' := z ≫ i
  let x := x' ≫ p
  let K := (upperStar AddCommGrpCat.{u + 1} p).obj G
  let F := (upperStar AddCommGrpCat.{u + 1} h).obj K
  let H := (lowerStar AddCommGrpCat.{u + 1} h).obj F
  let β := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app K
  have : IsAffine (Scheme.strictHenselizationScheme s) := by
    change IsAffine (Spec (Scheme.strictHenselizationRing s))
    infer_instance
  have ht : IsAffineHom t := inferInstance
  have hh : IsAffineHom h := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback f' t).flip ht
  have hclosed : x' ≫ f' = (z ≫ pullback.snd f'
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))) ≫
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)) := by
    simpa only [x', i, Category.assoc] using! congrArg (fun a ↦ z ≫ a)
      (pullback.condition (f := f') (g := Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationRingPointEvaluation s))))
  have hc := localAcyclicity_strict_fibre_comparison f s p f'
    (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)) x'
    (z ≫ pullback.snd f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationRingPointEvaluation s)))) hclosed t
  have hq := hc.1
  let e := Classical.choose hc.2
  let E := Classical.choose (Classical.choose_spec hc.2)
  have hE := (Classical.choose_spec (Classical.choose_spec hc.2)).1
  let ρ := Scheme.strictHenselizationStructuralMap x'
  let W := pullback h ρ
  let w := pullback.fst h ρ
  let k := pullback.snd h ρ
  let v := pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom)
  let g := Scheme.strictHenselizationStructuralMap x
  let q := asIso (localAcyclicityStrictMap p x')
  let E0 : W ≅ pullback (ρ ≫ f') t :=
    pullbackSymmetry h ρ ≪≫ pullbackRightPullbackFstIso f' t ρ
  let E' := E0 ≪≫ E
  have hqg : q.hom ≫ g = ρ ≫ p := by
    change localAcyclicityStrictMap p x' ≫ g = ρ ≫ p
    unfold localAcyclicityStrictMap
    exact (existsUnique_localAcyclicityStrictMap p x').choose_spec.1.1
  have hEtyped : E.hom ≫ v = pullback.fst (ρ ≫ f') t ≫ q.hom := by
    exact hE
  have hE' : E'.hom ≫ v = k ≫ q.hom := by
    dsimp only [E', Iso.trans_hom]
    erw [Category.assoc, hEtyped]
    change E0.hom ≫ pullback.fst (ρ ≫ f') t ≫ q.hom = k ≫ q.hom
    simp only [E0, Iso.trans_hom, Category.assoc,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    exact pullbackSymmetry_hom_comp_fst_assoc h ρ q.hom
  have htransport := globalSections_iso_over_transport
    (X := X) (Y := pullback f (Scheme.strictHenselizationStructuralMap s))
    (T := pullback f' t) (L := Scheme.strictHenselizationScheme x')
    (Z := Scheme.strictHenselizationScheme x)
    (W := W) (V := localAcyclicityFiber f x (t ≫ e.hom))
    p h ρ w k (pullback.condition (f := h) (g := ρ)) g v q E' hqg hE' G
  let U := Classical.choose htransport
  let V := Classical.choose (Classical.choose_spec htransport)
  have hUV := Classical.choose_spec (Classical.choose_spec htransport)
  let ΓL := Sheaf.Γ (Scheme.strictHenselizationScheme x').smallEtaleTopology
    AddCommGrpCat.{u + 1}
  let ΓW := Sheaf.Γ W.smallEtaleTopology AddCommGrpCat.{u + 1}
  let b := ΓL.map ((baseChangeMap AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback h ρ).toCommSq).app F) ≫
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} k).hom.app
      ((upperStar AddCommGrpCat.{u + 1} w).obj F)
  have hrH := restriction_isIso x' H
  have hex := isIso_strictLocalOrdinaryDirectImageComparison h x' F
  have hb : IsIso (restriction x' H ≫ b) := by
    dsimp only [b]
    infer_instance
  have hrK := restriction_isIso x' K
  have hrG := restriction_isIso x G
  let c := upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} i z
  let A := c.app K ≪≫ asIso (restriction x' K) ≪≫ U ≪≫ (asIso (restriction x G)).symm
  let B := c.app H ≪≫ asIso (restriction x' H ≫ b) ≪≫ V
  refine ⟨e, A, B, ?_⟩
  have hunit : ΓL.map ((upperStar AddCommGrpCat.{u + 1} ρ).map β) ≫ b =
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} k
        ((upperStar AddCommGrpCat.{u + 1} ρ).obj K) ≫
      ΓW.map ((squareUpperStarIso AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback h ρ).toCommSq).hom.app K) := by
    dsimp only [b]
    rw [← ΓL.map_comp_assoc, map_unit_baseChangeMap_app]
    rw [ΓL.map_comp, Category.assoc]
    erw [(lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} k).hom.naturality]
    rw [← Category.assoc]
    erw [← globalSectionsUpperStarMap_eq k
      ((upperStar AddCommGrpCat.{u + 1} ρ).obj K)]
  change (Scheme.pointSmallEtale z).sheafFiber.map
      ((upperStar AddCommGrpCat.{u + 1} i).map β) ≫
      ((c.app H).hom ≫ (restriction x' H ≫ b) ≫ V.hom) =
    ((c.app K).hom ≫ restriction x' K ≫ U.hom ≫ inv (restriction x G)) ≫
      localAcyclicityAlpha f x (t ≫ e.hom) G
  have hcβ := c.hom.naturality β
  dsimp only [Functor.comp_map] at hcβ
  rw [alpha_eq]
  exact comparison_chain _ _ _ _ _ _ _ _ _ _ V U _ (restriction x G)
    hcβ (restriction_naturality x' β) hunit hUV

end AlgebraicGeometry.Etale
