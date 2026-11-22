import Langlands.Global.AdelicStandardLeviCompactAssembly
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Global.FinitePlaceIwasawaLocalInput
import Langlands.Global.InfinitePlaceLeviIwasawaBaseChange
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactProof
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexProof
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.ParabolicWhiteheadIsomorphism
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof

/-! # One finite-place compact for all standard Levis from available buildings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.FinitePlaceGroupPoints

open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits
  Langlands.AlgebraicGeometry.PointTopology CompactIwasawa

local instance localTopology {k : Type u} [Field k] [TopologicalSpace k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffine H.X.left] :
    TopologicalSpace (rationalPoints H) := rationalPointTopology k H.X

section Local

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)

local instance localAffine {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

variable (D : KPBuildingAssignment.{u})

private abbrev building := (D.datum k G hG).base

local notation "B" => building hG D

set_option maxHeartbeats 1500000 in
private theorem isMaximalCompact_comap_specialCompact_of_centralizer
    (hD : D.IsValid) (nu : cocharacterLattice (B).S) (hnu : IsGenericCocharacter (B).i nu)
    (x : (B).Apartment) (hx : (B).apartment.IsSpecialApartmentVertex x)
    {M : GroupScheme (Spec (CommRingCat.of k))} [IsAffine M.X.left]
    (j : M ⟶ G) (hj : IsClosedSubgroup j) (xi : cocharacterLattice (B).S)
    (hxi : SubgroupFunctor.range j = Dynamic.centralizer (CommGroupScheme.groupHom xi ≫ (B).i)) :
    IsMaximalCompact (((B).apartment.specialCompactSubgroup x).comap (rationalPoints.map j)) := by
  let : Mono (B).i.hom.hom.left := (B).isMaximalSplitTorus.isSplitSubtorus.mono
  let : IsClosedImmersion j.hom.hom.left := hj
  let K := (B).apartment.specialCompactSubgroup x
  have hAvail := hD.isAvailableFor (F := k) (G := G) (hG := hG)
  have hIwas := ((Iwasawa.availableIwasawa k G hG D hAvail nu hnu).1 x hx)
  have hRoot := relativeRootSystem k G hG (B).S (B).i (B).isMaximalSplitTorus
  obtain ⟨n, hn⟩ := hRoot.exists_normalizerPoint_dominant (B).i
    (B).isMaximalSplitTorus.isSplitSubtorus.1 nu xi
  have hA := hAvail.satisfiesPartialBuildingAxioms
  obtain ⟨m, hm, hmn⟩ := SpecialCompact.WeylRepresentatives.special_parahoric_normalizer_surjective
    B hA.apartmentAxioms hA.hasZeroFixerGenerators
    (rootRankOneFactorization k G hG (B).S (B).i (B).isMaximalSplitTorus) nu hnu hx.1 (QuotientGroup.mk n)
  have hmK : m.val ∈ K := hIwas.2.1 hm
  let eta := cocharacterAut (normalizingAut (B).i n) xi
  let r := m / n
  have hr : r.val ∈ centralizerPoints (B).i :=
    (QuotientGroup.eq_iff_div_mem (N := (centralizerPoints (B).i).subgroupOf
      (normalizerPoints (B).i))).mp hmn
  have hrZ : (r : rationalPoints G) ∈ (torusCentralizer (B).i).carrier (Over.mk (𝟙 _)) := by
    rw [torusCentralizer_carrier_base]
    exact hr
  have hrEta := cocharacterAut_normalizingAut_eq_of_mem_dynamicCentralizer (B).i r
    (torusCentralizer_le_dynamicCentralizer (B).i (CommGroupScheme.groupHom eta) _ hrZ)
  have hmEta : cocharacterAut (normalizingAut (B).i m) xi = eta := by
    calc
      _ = cocharacterAut (normalizingAut (B).i (r * n)) xi := by rw [show r * n = m from div_mul_cancel m n]
      _ = eta := by rw [cocharacterAut_normalizingAut_mul]; exact hrEta
  let J := simpleRootFace (B).i nu eta
  have hJ : IsStandardCocharacter (B).i nu J eta :=
    isStandardCocharacter_simpleRootFace (B).i nu
      (fun a ha => hn a (simpleRelativeRoots_subset_positive (B).i nu ha))
  have hL := ((standardCocharacter k G hG (B).S (B).i (B).isMaximalSplitTorus nu hnu J hJ.1).2 eta hJ).2.1
  let mIso := G.innerIso m.val
  have hRange : (standardLevi (B).i nu J).comap mIso.hom = SubgroupFunctor.range j := by
    rw [hxi, hL, ← hmEta, groupHom_cocharacterAut_comp]
    exact (Dynamic.centralizer_eq_comap_of_iso _ _).symm
  let L := Standard.leviScheme (B).i nu J
  let incl := Standard.leviHom (B).i nu J
  let : IsAffineHom L.X.hom := (Standard.isClosedSubgroup_leviHom (B).i nu J).isAffineHom
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  let e := hrep.isoOfComap (Standard.isRepresentedBy_leviHom (B).i nu J) mIso hRange
  have he : e.hom ≫ incl = j ≫ mIso.hom := SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp _ _ _ _
  let ePts : rationalPoints M ≃ₜ* rationalPoints L :=
    { toMulEquiv := rationalPoints.mapEquiv e
      continuous_toFun := continuous_rationalPointMap k e.hom.hom.hom
      continuous_invFun := continuous_rationalPointMap k e.inv.hom.hom }
  obtain ⟨hLred, D', hD', _, _, x', hx', hK'⟩ :=
    SpecialCompact.availableSpecialLeviCompact k G hG D hD nu hnu x hx J hJ.1
  let : Smooth L.X.hom := hLred.smooth
  let : LocallyOfFiniteType L.X.hom := inferInstance
  let B' := (D'.datum k L hLred).base
  obtain ⟨nu', hnu'⟩ := B'.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B'.i
  have hMax' := ((Iwasawa.availableIwasawa k L hLred D' hD' nu' hnu').1 x' hx').2.2.2
  have hMax : IsMaximalCompact (K.comap (rationalPoints.map incl)) := by
    change B'.apartment.specialCompactSubgroup x' = K.comap (rationalPoints.map incl) at hK'
    rw [← hK']
    exact ⟨hMax'.1, fun L' hc hle => (hMax'.2.2.eq_of_le hc hle).symm⟩
  have hComp (y : rationalPoints M) :
      rationalPoints.map incl (ePts y) = m.val * rationalPoints.map j y * m.val⁻¹ := by
    change rationalPoints.map (e.hom ≫ incl) y = _
    rw [he]
    change rationalPoints.map mIso.hom (rationalPoints.map j y) = _
    rw [rationalPoints_map_innerIso]
    rfl
  have hPre : (K.comap (rationalPoints.map incl)).map ePts.symm.toMonoidHom =
      K.comap (rationalPoints.map j) := by
    calc
      _ = (K.comap (rationalPoints.map incl)).comap ePts.toMulEquiv.toMonoidHom :=
        (Subgroup.comap_equiv_eq_map_symm ePts.toMulEquiv _).symm
      _ = K.comap (rationalPoints.map j) := by
        ext y
        change rationalPoints.map incl (ePts y) ∈ K ↔ rationalPoints.map j y ∈ K
        rw [hComp, K.mul_mem_cancel_right (K.inv_mem hmK), K.mul_mem_cancel_left hmK]
  rw [← hPre]
  exact hMax.map ePts.symm

end Local

/-- Available corrected Bruhat–Tits data give the required simultaneous compact
on the actual finite completion at each finite place. -/
def FinitePlaceStandardLeviCompactReductionStatement : Prop :=
  BruhatTitsAvailabilityStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (v : FinitePlace F),
    ∃ K, fam.IsStandardLeviCompact (.inr v) K

set_option maxHeartbeats 1500000 in
theorem finitePlaceStandardLeviCompactReduction : FinitePlaceStandardLeviCompactReductionStatement.{u} := by
  intro hBuilding F _ _ G _ _ _ fam v
  obtain ⟨D, hD⟩ := hBuilding
  let k := FiniteCompletion F v
  let : ValuativeRel k := FiniteCompletion.valuativeRel v
  let : IsNonarchimedeanLocalField k := FiniteCompletion.isNonarchimedeanLocalField v
  let b := Spec.algebraMap F k
  let C := GroupScheme.baseChange b
  let Gv := baseChangedGroup F G v
  let hGv := baseChanged_isConnectedReductive F G fam.connectedReductive v
  let : IsAffineHom Gv.X.hom := hGv.isAffineHom
  let : IsAffine Gv.X.left := isAffine_of_isAffineHom Gv.X.hom
  let : Smooth Gv.X.hom := hGv.smooth
  let : LocallyOfFiniteType Gv.X.hom := inferInstance
  let Tv := (CommGroupScheme.baseChange b).obj fam.T
  have hTv : IsSplitSubtorus (T := Tv) (C.map fam.i) :=
    ⟨fam.maximalSplit.isSplitSubtorus.1.baseChange b, fam.maximalSplit.isSplitSubtorus.2.baseChange b⟩
  obtain ⟨S, i, hi, f, hf⟩ := exists_maximalSplitTorus_extension (T := Tv) Gv (C.map fam.i) hTv
  obtain ⟨D', hD', hS, hi'⟩ := SpecialCompact.validAssignmentTorusRebasing D hD k Gv hGv S i hi
  let B := (D'.datum k Gv hGv).base
  subst S
  have hiEq : B.i = i := eq_of_heq hi'
  subst i
  obtain ⟨nu, hnu⟩ := B.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B.i
  have hAvail := hD'.isAvailableFor (F := k) (G := Gv) (hG := hGv)
  obtain ⟨x, hx⟩ := SpecialCompact.availableSpecialVertexExistence k Gv hGv D' hAvail
  let K := B.apartment.specialCompactSubgroup x
  have hIwas := ((Iwasawa.availableIwasawa k Gv hGv D' hAvail nu hnu).1 x hx)
  let eG := baseChangeContinuousMulEquiv F G v
  let p₀ := fam.p fam.minimalIndex
  have hp₀ := baseChange_isParabolicSubgroup F G fam.connectedReductive p₀
    (fam.isCompatible fam.minimalIndex).parabolic v
  have hK₀ := hIwas.2.2.2.isLocalIwasawaCompact (C.map p₀) (hIwas.2.2.1.1 _ _ hp₀)
  refine ⟨K.map eG.toMonoidHom,
    hK₀.map eG (baseChangeMulEquiv F (fam.P fam.minimalIndex) v) (baseChangeMulEquiv_map F G p₀ v), ?_⟩
  intro J
  let j := fam.l J ≫ fam.p J
  let eM := baseChangeContinuousMulEquiv F (fam.M J) v
  have hj : IsClosedSubgroup (C.map j) :=
    ((fam.isCompatible J).levi.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup).baseChange b
  let : IsClosedImmersion (C.map j).hom.hom.left := hj
  let : IsAffine (C.obj (fam.M J)).X.left := isAffine_of_isAffineHom (C.map j).hom.hom.left
  obtain ⟨z, hz⟩ := StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer
    fam.connectedReductive fam.maximalSplit.isSplitSubtorus.1 fam.i fam.ν J.val
  let xi : cocharacterLattice B.S :=
    Additive.ofMul (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom z) ≫ f)
  have he : CommGroupScheme.groupHom xi ≫ B.i =
      Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom z ≫ fam.i) := by
    change (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom z) ≫ f) ≫ B.i = _
    rw [Category.assoc, hf, Dynamic.baseChangeCocharacter_comp_hom]
  have hxi : SubgroupFunctor.range (C.map j) = Dynamic.centralizer (CommGroupScheme.groupHom xi ≫ B.i) := by
    rw [he, Dynamic.centralizer_baseChange, SubgroupFunctor.range_baseChangeHom]
    exact congrArg (SubgroupFunctor.baseChange b) ((fam.isCompatible J).levi_eq.trans hz)
  have hMax := isMaximalCompact_comap_specialCompact_of_centralizer hGv D' hD' nu hnu x hx
    (C.map j) hj xi hxi
  change IsMaximalCompact ((K.map eG.toMonoidHom).comap
    ((fam.M J).affinePointsTarget j (CommAlgCat.of F k)))
  rw [comap_map_eq_of_comm _ _ eM.toMulEquiv eG.toMulEquiv
    (fun y => (baseChangeMulEquiv_map F G j v y).symm)]
  exact hMax.map eM

end Langlands.Global.FinitePlaceGroupPoints
