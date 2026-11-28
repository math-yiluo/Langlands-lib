import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.GroupScheme.Rational.StandardMinimalLeviMultiplication
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.GmOrbitInversion
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.AffinePointRingPointComparison
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineGroupProofs

/-! # A compact-factor neighborhood in the standard archimedean open cell -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology Set NumberField
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "U" => Standard.unipotentScheme i ν ∅
local notation "M" => Standard.leviScheme i (-ν) ∅
local notation "V" => Standard.unipotentScheme i (-ν) ∅
local notation "P" => Standard.parabolicScheme i (-ν) ∅
local notation "iU" => Standard.unipotentHom i ν ∅
local notation "iM" => Standard.leviHom i (-ν) ∅
local notation "iV" => Standard.unipotentHom i (-ν) ∅
local notation "iP" => Standard.parabolicHom i (-ν) ∅

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem isOpenImmersion_oppositeCell
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i (-ν)) :
    IsOpenImmersion ((fst (U).X (P).X ≫ (iU).hom.hom) * (snd (U).X (P).X ≫ (iP).hom.hom)).left := by
  let : Smooth G.X.hom := hG.smooth
  let cochar := CommGroupScheme.groupHom (-ν) ≫ i
  have hcochar : CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ cochar =
      CommGroupScheme.groupHom ν ≫ i := by
    have h := GmOrbitInversion.comp_groupHom_neg (𝟙 (Gm (Spec (CommRingCat.of F))).X) (-ν)
    simp only [neg_neg, Category.id_comp] at h
    apply Grp.hom_ext
    simp only [cochar, Grp.comp_hom_hom, ← Category.assoc, ← h]
  apply oppositeCellStatement F G cochar U P iU iP
  · rw [hcochar, ← standardUnipotent_empty_eq_dynamic i ν hG hi]
    exact Standard.isRepresentedBy_unipotentHom i ν ∅
  · change (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)).IsRepresentedBy iP
    rw [← standardParabolic_empty_eq_dynamic_of_generic i (-ν) hG hi hν]
    exact Standard.isRepresentedBy_parabolicHom i (-ν) ∅

section Local

variable (S : Type) [CommRing S] [Algebra F S] [TopologicalSpace S]
  [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

local notation "A" => CommAlgCat.of F S

local instance openCellPointTopology (H : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (H.affinePoints A) := H.affinePointsTopologicalSpace A

omit [LocallyOfFiniteType G.X.hom] in
private theorem local_openCell_mem_nhds
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i (-ν))
    [IsAffine (U).X.left] [IsAffine (M).X.left] [IsAffine (V).X.left]
    {ZU : Set ((U).affinePoints A)} {ZM : Set ((M).affinePoints A)} {ZV : Set ((V).affinePoints A)}
    (hU : ZU ∈ 𝓝 1) (hM : ZM ∈ 𝓝 1) (hV : ZV ∈ 𝓝 1) :
    {x : G.affinePoints A | ∃ u ∈ ZU, ∃ m ∈ ZM, ∃ v ∈ ZV,
      x = (u ≫ (iU).hom.hom) * (m ≫ (iM).hom.hom) * (v ≫ (iV).hom.hom)} ∈ 𝓝 1 := by
  let : IsAffineHom (P).X.hom := (Standard.isClosedSubgroup_parabolicHom i (-ν) ∅).isAffineHom
  let : IsAffine (P).X.left := isAffine_of_isAffineHom (P).X.hom
  let : IsAffine ((U).X ⊗ (P).X).left := tensor_isAffine F (U).X (P).X
  let X := (U).X ⊗ (P).X
  let E := Standard.emptyLeviMultiplicationIso i (-ν) hG hi hν
  let fU : X ⟶ (U).X := fst (U).X (P).X
  let fP : X ⟶ (P).X := snd (U).X (P).X
  let fM : X ⟶ (M).X := fP ≫ E.inv ≫ fst (M).X (V).X
  let fV : X ⟶ (V).X := fP ≫ E.inv ≫ snd (M).X (V).X
  let f : X ⟶ G.X := (fU ≫ (iU).hom.hom) * (fP ≫ (iP).hom.hom)
  let : IsOpenImmersion f.left := isOpenImmersion_oppositeCell i ν hG hi hν
  let e : RingPoint F X S := lift (1 : (U).affinePoints A) (1 : (P).affinePoints A)
  have hm : IsOpenEmbedding (Y := RingPoint F G.X S) (fun p : RingPoint F X S => p ≫ f) := by
    have h := isOpenEmbedding_schemePointMap F S f
    change @IsOpenEmbedding (RingPoint F X S) (RingPoint F G.X S)
      (schemePointTopology F X S) (schemePointTopology F G.X S) (fun p => p ≫ f) at h
    rw [schemePointTopology_eq_affine F X S, schemePointTopology_eq_affine F G.X S] at h
    exact h
  let kU (p : RingPoint F X S) : (U).affinePoints A := p ≫ fU
  let kM (p : RingPoint F X S) : (M).affinePoints A := p ≫ fM
  let kV (p : RingPoint F X S) : (V).affinePoints A := p ≫ fV
  have hcU : Continuous kU := by
    convert ((U).affinePointsRingPointHomeomorph A).symm.continuous.comp
      (continuous_affineSchemePointMap F S fU) using 1
    funext p
    exact ((U).affinePointsRingPointHomeomorph_symm_apply A (p ≫ fU)).symm
  have hcM : Continuous kM := by
    convert ((M).affinePointsRingPointHomeomorph A).symm.continuous.comp
      (continuous_affineSchemePointMap F S fM) using 1
    funext p
    exact ((M).affinePointsRingPointHomeomorph_symm_apply A (p ≫ fM)).symm
  have hcV : Continuous kV := by
    convert ((V).affinePointsRingPointHomeomorph A).symm.continuous.comp
      (continuous_affineSchemePointMap F S fV) using 1
    funext p
    exact ((V).affinePointsRingPointHomeomorph_symm_apply A (p ≫ fV)).symm
  have hp₁ : lift (1 : (M).affinePoints A) (1 : (V).affinePoints A) ≫ E.hom =
      (1 : (P).affinePoints A) := by
    rw [Standard.comp_emptyLeviMultiplicationIso_hom]
    simp only [MonObj.one_comp, one_mul]
  have hp₁_inv : (1 : (P).affinePoints A) ≫ E.inv =
      lift (1 : (M).affinePoints A) (1 : (V).affinePoints A) := by
    rw [← hp₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1U : kU e = 1 := lift_fst _ _
  have h1M : kM e = 1 := by
    change lift _ _ ≫ snd (U).X (P).X ≫ E.inv ≫ fst (M).X (V).X = (1 : (M).affinePoints A)
    rw [lift_snd_assoc, ← Category.assoc, hp₁_inv, lift_fst]
  have h1V : kV e = 1 := by
    change lift _ _ ≫ snd (U).X (P).X ≫ E.inv ≫ snd (M).X (V).X = (1 : (V).affinePoints A)
    rw [lift_snd_assoc, ← Category.assoc, hp₁_inv, lift_snd]
  let mulCell (p : RingPoint F X S) : G.affinePoints A := p ≫ f
  have h1f : mulCell e = 1 := by
    change lift (1 : (U).affinePoints A) (1 : (P).affinePoints A) ≫
      ((fst (U).X (P).X ≫ (iU).hom.hom) * (snd (U).X (P).X ≫ (iP).hom.hom)) =
      (1 : G.affinePoints A)
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.one_comp, one_mul]
  have hnear : kU ⁻¹' ZU ∩ kM ⁻¹' ZM ∩ kV ⁻¹' ZV ∈ 𝓝 e :=
    inter_mem (inter_mem (hcU.continuousAt.preimage_mem_nhds (by rwa [h1U]))
      (hcM.continuousAt.preimage_mem_nhds (by rwa [h1M])))
      (hcV.continuousAt.preimage_mem_nhds (by rwa [h1V]))
  have hm' : IsOpenEmbedding mulCell := by
    convert (G.affinePointsRingPointHomeomorph A).symm.isOpenEmbedding.comp hm using 1
    funext p
    exact (G.affinePointsRingPointHomeomorph_symm_apply A (p ≫ f)).symm
  have himg := hm'.isOpenMap.image_mem_nhds hnear
  rw [h1f] at himg
  refine mem_of_superset himg ?_
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨kU p, hp.1.1, kM p, hp.1.2, kV p, hp.2, ?_⟩
  have hpair : lift (kM p) (kV p) = (p ≫ fP) ≫ E.inv := by
    apply CartesianMonoidalCategory.hom_ext <;> simp only
      [lift_fst, lift_snd, kM, kV, fM, fV, Category.assoc]
  have hmult : (p ≫ fP : (P).affinePoints A) =
      (kM p ≫ (Standard.leviToParabolic i (-ν) ∅).hom.hom) *
        (kV p ≫ (Standard.unipotentToParabolic i (-ν) ∅).hom.hom) := by
    rw [← Standard.comp_emptyLeviMultiplicationIso_hom i (-ν) hG hi hν, hpair, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  change p ≫ f = (kU p ≫ (iU).hom.hom) * (kM p ≫ (iM).hom.hom) * (kV p ≫ (iV).hom.hom)
  rw [show (p ≫ f : G.affinePoints A) =
      (kU p ≫ (iU).hom.hom) * (((p ≫ fP) ≫ (iP).hom.hom) : G.affinePoints A) by
    simp only [f, kU, MonObj.comp_mul, Category.assoc]]
  rw [hmult, MonObj.mul_comp, mul_assoc]
  congr 1
  simp only [Category.assoc, ← Grp.comp_hom_hom, Standard.leviToParabolic_comp,
    Standard.unipotentToParabolic_comp]

end Local

section Archimedean

variable [NumberField F]

local notation "Points" => InfiniteAdelicGroupPoints F

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [NumberField F] in
private theorem atPlace_postcomp {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (f : H ⟶ G) (x : Points H) (w : InfinitePlace F) :
    InfiniteAdelicGroupPoints.atPlace F G w (x ≫ f.hom.hom) =
      InfiniteAdelicGroupPoints.atPlace F H w x ≫ f.hom.hom :=
  DFunLike.congr_fun (H.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (Pi.evalAlgHom F (fun v : InfinitePlace F => v.Completion) w))) x

/-- Compact subsets of the positive radical, the opposite Levi and the
opposite radical have a product that contains an archimedean identity neighborhood. -/
theorem exists_compact_archimedean_openCell
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ∃ (CU : Set (Points U)) (CM : Set (Points M)) (CV : Set (Points V)),
      IsCompact CU ∧ IsCompact CM ∧ IsCompact CV ∧
      {x : Points G | ∃ u ∈ CU, ∃ m ∈ CM, ∃ v ∈ CV,
        x = (u ≫ (iU).hom.hom) * (m ≫ (iM).hom.hom) * (v ≫ (iV).hom.hom)} ∈ 𝓝 1 := by
  classical
  let hU := Standard.isClosedSubgroup_unipotentHom i ν ∅
  let hM := Standard.isClosedSubgroup_leviHom i (-ν) ∅
  let hV := Standard.isClosedSubgroup_unipotentHom i (-ν) ∅
  let : IsAffineHom (U).X.hom := hU.isAffineHom
  let : IsAffineHom (M).X.hom := hM.isAffineHom
  let : IsAffineHom (V).X.hom := hV.isAffineHom
  let : IsAffine (U).X.left := isAffine_of_isAffineHom (U).X.hom
  let : IsAffine (M).X.left := isAffine_of_isAffineHom (M).X.hom
  let : IsAffine (V).X.left := isAffine_of_isAffineHom (V).X.hom
  let : LocallyOfFiniteType (U).X.hom := hU.locallyOfFiniteType
  let : LocallyOfFiniteType (M).X.hom := hM.locallyOfFiniteType
  let : LocallyOfFiniteType (V).X.hom := hV.locallyOfFiniteType
  have hν' : IsGenericCocharacter i (-ν) := by
    intro α hα
    simpa only [map_neg, neg_ne_zero] using hν α hα
  have hbox (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left]
      [LocallyOfFiniteType H.X.hom] (w : InfinitePlace F) :
      ∃ C : Set (InfinitePlaceGroupPoints F H w), IsCompact C ∧ C ∈ 𝓝 1 := by
    let : LocallyCompactSpace (InfinitePlaceGroupPoints F H w) :=
      H.affinePointsLocallyCompactSpace (CommAlgCat.of F w.Completion)
    exact exists_compact_mem_nhds (1 : InfinitePlaceGroupPoints F H w)
  choose CU hCU hCUn using hbox U
  choose CM hCM hCMn using hbox M
  choose CV hCV hCVn using hbox V
  let CUi := InfiniteAdelicGroupPoints.assemble F U '' Set.pi univ CU
  let CMi := InfiniteAdelicGroupPoints.assemble F M '' Set.pi univ CM
  let CVi := InfiniteAdelicGroupPoints.assemble F V '' Set.pi univ CV
  refine ⟨CUi, CMi, CVi,
    (isCompact_univ_pi hCU).image (InfiniteAdelicGroupPoints.continuous_assemble F U),
    (isCompact_univ_pi hCM).image (InfiniteAdelicGroupPoints.continuous_assemble F M),
    (isCompact_univ_pi hCV).image (InfiniteAdelicGroupPoints.continuous_assemble F V), ?_⟩
  let cells (w : InfinitePlace F) :=
    {x : InfinitePlaceGroupPoints F G w | ∃ u ∈ CU w, ∃ m ∈ CM w, ∃ v ∈ CV w,
      x = (u ≫ (iU).hom.hom) * (m ≫ (iM).hom.hom) * (v ≫ (iV).hom.hom)}
  have hcells (w : InfinitePlace F) : cells w ∈ 𝓝 1 :=
    local_openCell_mem_nhds i ν w.Completion hG hi hν' (hCUn w) (hCMn w) (hCVn w)
  have hprod : Set.pi univ cells ∈
      𝓝 (1 : (w : InfinitePlace F) → InfinitePlaceGroupPoints F G w) :=
    set_pi_mem_nhds Set.finite_univ fun w _ => hcells w
  have hpre : InfiniteAdelicGroupPoints.completions F G ⁻¹' Set.pi univ cells ∈ 𝓝 (1 : Points G) :=
    (InfiniteAdelicGroupPoints.completions F G).continuous.continuousAt.preimage_mem_nhds (by
      change Set.pi univ cells ∈ 𝓝 (InfiniteAdelicGroupPoints.completions F G (1 : Points G))
      rw [map_one]
      exact hprod)
  exact mem_of_superset hpre fun x hx => by
    have hxloc (w : InfinitePlace F) : InfiniteAdelicGroupPoints.atPlace F G w x ∈ cells w :=
      hx w (mem_univ w)
    choose u hu m hm v hv heq using hxloc
    refine ⟨InfiniteAdelicGroupPoints.assemble F U u, ⟨u, fun w _ => hu w, rfl⟩,
      InfiniteAdelicGroupPoints.assemble F M m, ⟨m, fun w _ => hm w, rfl⟩,
      InfiniteAdelicGroupPoints.assemble F V v, ⟨v, fun w _ => hv w, rfl⟩, ?_⟩
    apply (InfiniteAdelicGroupPoints.completions F G).injective
    funext w
    simp only [InfiniteAdelicGroupPoints.completions_apply, map_mul, atPlace_postcomp,
      InfiniteAdelicGroupPoints.atPlace_assemble]
    exact heq w

end Archimedean

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

open GroupScheme AdelicSiegelFactors

/-- A compact-factor neighborhood for the actual archimedean points of
the standard open cell with the positive radical first. -/
def StandardArchimedeanOpenCellStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T),
      IsMaximalSplitTorus i → IsGenericCocharacter i ν →
      ∃ (CU : Set (InfiniteAdelicGroupPoints F (Standard.unipotentScheme i ν ∅)))
        (CM : Set (InfiniteAdelicGroupPoints F (Standard.leviScheme i (-ν) ∅)))
        (CV : Set (InfiniteAdelicGroupPoints F (Standard.unipotentScheme i (-ν) ∅))),
        IsCompact CU ∧ IsCompact CM ∧ IsCompact CV ∧
          {x : InfiniteAdelicGroupPoints F G | ∃ u ∈ CU, ∃ m ∈ CM, ∃ v ∈ CV,
            x = (u ≫ (Standard.unipotentHom i ν ∅).hom.hom) *
              (m ≫ (Standard.leviHom i (-ν) ∅).hom.hom) *
              (v ≫ (Standard.unipotentHom i (-ν) ∅).hom.hom)} ∈ 𝓝 1

theorem standardArchimedeanOpenCell : StandardArchimedeanOpenCellStatement := by
  intro F _ _ G _ _ _ hG T i ν hi hν
  exact exists_compact_archimedean_openCell i ν hG hi hν

end Langlands.Global
