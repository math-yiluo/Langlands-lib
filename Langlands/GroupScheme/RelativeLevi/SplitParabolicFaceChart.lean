import Langlands.GroupScheme.RelativeLevi.SplitFaceWeightData

/-! # Actual split parabolic charts with unscaled face heights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

variable {R : Type u} [CommRing R]
  {U G : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}

/-- Replacing weights by another family with the same zero roots preserves
the represented ambient positive term on every scheme test. -/
theorem isRepresentedBy_zeroInclusion_of_sameZero
    (W W' : RootWeightData C) (h : ∀ k, W.weight k = 0 ↔ W'.weight k = 0)
    (j : U ⟶ G) [Mono j.hom.hom] (F : SubgroupFunctor G)
    (hF : F.IsRepresentedBy (W'.inclusion 0 ≫ j)) :
    F.IsRepresentedBy (W.inclusion 0 ≫ j) := by
  have hs : W.subgroup 0 = W'.subgroup 0 := W.subgroup_zero_eq_of_zero_iff W' h
  have hW : (W'.subgroup 0).IsRepresentedBy (W.inclusion 0) :=
    ⟨(W.isRepresentedBy_inclusion 0).1, (W.isRepresentedBy_inclusion 0).2.trans hs⟩
  let e : W.groupScheme 0 ≅ W'.groupScheme 0 :=
    hW.isoOfIsRepresentedBy (W'.isRepresentedBy_inclusion 0)
  have he : e.hom ≫ W'.inclusion 0 = W.inclusion 0 :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _
  have : Mono (W.inclusion 0).hom.hom := (W.isRepresentedBy_inclusion 0).1
  have hmono : Mono (W.inclusion 0 ≫ j).hom.hom := by
    change Mono ((W.inclusion 0).hom.hom ≫ j.hom.hom)
    infer_instance
  refine ⟨hmono, ?_⟩
  have he' : e.hom ≫ (W'.inclusion 0 ≫ j) = W.inclusion 0 ≫ j := by
    rw [← Category.assoc, he]
  rw [← he', SubgroupFunctor.range_iso_comp, hF.2]

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData

namespace Langlands.GroupScheme

open LocalSplitCell RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [Finite J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ))
  (fam : J → (Ga R ⟶ G)) (wt : I → ℤ)

local instance splitParabolicFaceChart_affineSource : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- An actual regular root chart together with unscaled integral face weights
and the all-test identification of its positive term with the original U(wt). -/
structure SplitParabolicFaceChart where
  cocharacter : I → ℤ
  regular : ∀ a : J, coPairing (P.root a) cocharacter ≠ 0
  base : P.Base
  faceCoweight : I → ℤ
  coweight_eq : ∀ a, P.root' a faceCoweight = coPairing (P.root a) wt
  dominant : ∀ a ∈ base.support, 0 ≤ P.root' a faceCoweight
  chart : RootHeightChart (AffineRegularBorel.contractingGroup i cocharacter)
  index : Fin chart.dimension ≃ {a // base.IsPos a}
  root_comp : ∀ k, chart.roots (ULift.up k) ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i cocharacter) =
      fam (index k)
  weights : RootWeightData chart
  weight_eq : ∀ k, (weights.weight k : ℤ) =
    faceHeight base faceCoweight (P.rootSpanMem ℤ (index k))
  represented : (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).IsRepresentedBy
    (weights.inclusion 0 ≫
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i cocharacter))

variable {i P fam wt}

/-- Reductivity and actual root parametrizations construct a canonical based
face-weight chart for every coordinate cocharacter, including its zero roots. -/
theorem nonempty_splitParabolicFaceChart
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a)) :
    Nonempty (SplitParabolicFaceChart i P fam wt) := by
  classical
  let : P.IsReduced := hP.isReduced
  obtain ⟨b, hb⟩ := exists_base_nonnegative_coPairing P wt
  obtain ⟨reg, hregpos, hregneg⟩ := exists_cocharacter_of_base P b
  let cv := P.flip.toPerfPair.symm (coPairingLinear wt)
  have hcv (a : J) : P.root' a cv = coPairing (P.root a) wt := by
    change (P.flip.toPerfPair cv) (P.root a) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hdom : ∀ a ∈ b.support, 0 ≤ P.root' a cv := by
    intro a ha
    rw [hcv]
    exact hb a (b.isPos_of_mem_support ha)
  let neg := (Finite.equivFin {a // ¬ b.IsPos a}).symm
  let pos := (Finite.equivFin {a // b.IsPos a}).symm
  let n := Nat.card {a // b.IsPos a}
  let hu : TorusEquivariant i (fun a => P.root a) fam :=
    fun a T t c => (hfam a).equivariant T t c
  let : IsOpenImmersion
      (cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  have hpos (k : Fin n) : 0 < coPairing (P.root (pos k)) reg :=
    hregpos _ (pos k).property
  have hneg (k : Fin (Nat.card {a // ¬ b.IsPos a})) :
      coPairing (P.root (neg k)) reg < 0 :=
    hregneg _ (neg k).property
  have hwt (k : Fin n) : 0 ≤ coPairing (P.root (pos k)) wt :=
    hb _ (pos k).property
  have hnegwt (k : Fin (Nat.card {a // ¬ b.IsPos a})) :
      coPairing (P.root (neg k)) wt ≤ 0 := by
    let := P.indexNeg
    have h := hb (- (neg k : J))
      ((RootPairing.Base.IsPos.neg_iff_not b (neg k)).mpr (neg k).property)
    have he : P.root (- (neg k : J)) = - P.root (neg k) := by
      change P.root (P.reflectionPerm (neg k) (neg k)) = _
      simp
    change 0 ≤ coPairingLinear wt (P.root (- (neg k : J))) at h
    rw [he, map_neg] at h
    change 0 ≤ - coPairing (P.root (neg k)) wt at h
    omega
  let : IsAffineHom (AffineRegularBorel.contractingGroup i reg).X.hom :=
    AffineRegularBorel.isAffineHom_contractingGroup i reg
  let : IsAffine (AffineRegularBorel.contractingGroup i reg).X.left :=
    isAffine_of_isAffineHom (AffineRegularBorel.contractingGroup i reg).X.hom
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i reg)
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom
    (AffineRegularBorel.cocharacter i reg)
  let C := positiveCellRootHeightChart j hu reg hU hpos hneg
  let W := positiveCellRootFaceWeightData j hu reg hU hpos hneg b cv
    (fun k => (pos k).property)
  let W' := positiveCellRootWeightData j hu reg hU hpos hneg wt hwt
  have hW (k : Fin n) : (W.weight k : ℤ) =
      faceHeight b cv (P.rootSpanMem ℤ (pos k)) :=
    Int.toNat_of_nonneg (faceHeight_nonneg_of_isPos b cv (pos k).property)
  have hW' (k : Fin n) : (W'.weight k : ℤ) = coPairing (P.root (pos k)) wt :=
    Int.toNat_of_nonneg (hwt k)
  have hz (k : Fin n) : W.weight k = 0 ↔ W'.weight k = 0 := by
    have hval := faceHeight_pos_iff_of_nonneg b cv hdom (pos k)
      (by rw [hcv]; exact hwt k)
    rw [hcv, ← hW k, ← hW' k] at hval
    omega
  have hroot (k : Fin n) : C.roots (ULift.up k) ≫ j = fam (pos k) :=
    rootToUnipotent_comp j hu reg hU (pos k) (hpos k)
  let : Mono j.hom.hom := hU.1
  let : IsAffineHom (AffineRegularBorel.contractingGroup i wt).X.hom :=
    AffineRegularBorel.isAffineHom_contractingGroup i wt
  let : IsAffine (AffineRegularBorel.contractingGroup i wt).X.left :=
    isAffine_of_isAffineHom (AffineRegularBorel.contractingGroup i wt).X.hom
  let : IsOpenImmersion
      (cellMap i fam (fun k => (neg k : J))
        (fun k : Fin C.dimension => (pos k : J))).left :=
    LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  have hrep := isRepresentedBy_positiveWeightInclusion
    (neg := fun k => (neg k : J)) (pos := fun k => (pos k : J))
    C W' j hroot hu wt hW' hnegwt
    (Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i wt))
    (Dynamic.Affine.isRepresentedBy_unipotentHom (AffineRegularBorel.cocharacter i wt))
  refine ⟨{
    cocharacter := reg
    regular := ?_
    base := b
    faceCoweight := cv
    coweight_eq := hcv
    dominant := hdom
    chart := C
    index := pos
    root_comp := hroot
    weights := W
    weight_eq := hW
    represented := W.isRepresentedBy_zeroInclusion_of_sameZero W' hz j _ hrep
  }⟩
  intro a
  by_cases ha : b.IsPos a
  · exact ne_of_gt (hregpos a ha)
  · exact ne_of_lt (hregneg a ha)

namespace SplitParabolicFaceChart

variable (C : SplitParabolicFaceChart i P fam wt)

/-- The actual unscaled face-weight positive term is isomorphic to the
original cocharacter's actual contracting group. -/
def dynamicIso : C.weights.groupScheme 0 ≅ AffineRegularBorel.contractingGroup i wt :=
  C.represented.isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_unipotentHom (AffineRegularBorel.cocharacter i wt))

omit [Finite J] in
/-- The canonical based face-weight comparison preserves the ambient inclusion. -/
theorem dynamicIso_hom_comp :
    C.dynamicIso.hom ≫ Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i wt) =
      C.weights.inclusion 0 ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

omit [Finite J] in
include C in
/-- The actual positive face-weight term supplies a finite vector-bundle
series for the original contracting group. -/
theorem hasFiniteVectorBundleSeries :
    HasFiniteVectorBundleSeries (AffineRegularBorel.contractingGroup i wt) :=
  HasFiniteVectorBundleSeries.of_iso C.dynamicIso
    (RootWeightData.hasFiniteVectorBundleSeries C.weights)

end SplitParabolicFaceChart

end Langlands.GroupScheme
