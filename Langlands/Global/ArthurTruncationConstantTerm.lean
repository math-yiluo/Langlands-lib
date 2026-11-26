import Langlands.Global.ArthurTruncation
import Langlands.Global.AdelicStandardConstantTermIntegral
import Langlands.Global.AdelicLeviFiniteVolume
import Langlands.Global.AdelicSubgroupQuotientTransport
import Langlands.Automorphic.GroupSchemeConstantTermConjugation
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.GroupScheme.RelativeLevi.SplitFaceCoordinateConjugacy

/-! # Constant terms of locally bounded functions on a rational parabolic quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T}

local notation "Points" => AdelicGroupPoints F G
local notation "p[" J "]" => Standard.parabolicHom i ν J
local notation "u[" J "]" => Standard.unipotentHom i ν J
local notation "V[" J "]" => SubgroupFunctor.range (u[J])

omit [LocallyOfFiniteType G.X.hom] in
/-- The rational-parabolic image used in truncation is the usual image of principal points. -/
theorem parabolicRationalImage_eq_rationalImage (J : Set (characterLattice T)) :
    parabolicRationalImage (F := F) (p[J]) = rationalImage F (p[J]) := by
  rw [parabolicRationalImage, parabolicRationalSubgroup, Subgroup.subgroupOf_map_subtype,
    ← rationalImage_eq_map, inf_eq_left.mpr (rationalImage_le_rationalSubgroup (p[J]))]

section Quotient

open AdelicSubgroupPoints in
private def quotientEval (V : SubgroupFunctor G) (φ : Points → ℂ) (x : Points)
    (c : AdelicSubgroupPoints.RationalQuotient F G V) : ℂ :=
  φ ((c.out : adelicPoints F G V).val * x)

open AdelicSubgroupPoints in
omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem quotientEval_mk (V : SubgroupFunctor G) (φ : Points → ℂ)
    (hφ : ∀ v ∈ AdelicSubgroupPoints.rationalSubgroup F G V, ∀ x, φ ((v : Points) * x) = φ x)
    (x : Points) (v : adelicPoints F G V) :
    quotientEval V φ x (LeftCosetSpace.mk _ v) = φ ((v : Points) * x) := by
  let f (n : adelicPoints F G V) := φ ((n : Points) * x)
  have hf (a : AdelicSubgroupPoints.rationalSubgroup F G V) (n : adelicPoints F G V) :
      f (a.val * n) = f n := by
    change φ (((a.val * n : adelicPoints F G V) : Points) * x) = φ ((n : Points) * x)
    rw [Subgroup.coe_mul, mul_assoc, hφ _ a.2]
  change f (LeftCosetSpace.mk _ v).out = f v
  rw [congrFun (RankinSelbergGlobal.Unfolding.out_eq_lift _ f hf) (LeftCosetSpace.mk _ v)]
  rfl

open AdelicSubgroupPoints in
private theorem integral_quotientEval_conj (V W : SubgroupFunctor G)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (hW : W = V.comap (G.innerIso a).hom)
    [IsClosed (adelicPoints F G V : Set Points)] [IsClosed (adelicPoints F G W : Set Points)]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V)]
    (φ : Points → ℂ)
    (hφV : ∀ v ∈ AdelicSubgroupPoints.rationalSubgroup F G V, ∀ x, φ ((v : Points) * x) = φ x)
    (hφW : ∀ v ∈ AdelicSubgroupPoints.rationalSubgroup F G W, ∀ x, φ ((v : Points) * x) = φ x)
    (hφa : ∀ x, φ (innerAdelicPoint F G a * x) = φ x) (x : Points) :
    (∫ c, quotientEval V φ (innerAdelicPoint F G a * x) c
      ∂normalizedRationalQuotientHaarMeasure F G V) =
    ∫ c, quotientEval W φ x c ∂normalizedRationalQuotientHaarMeasure F G W := by
  subst W
  rw [← integral_comp_rationalQuotientIso F (G.innerIso a) V]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro c
  induction c using Quotient.inductionOn with
  | _ v =>
    change quotientEval V φ (innerAdelicPoint F G a * x)
      (rationalQuotientIso F (G.innerIso a) V (LeftCosetSpace.mk _ v)) =
      quotientEval _ φ x (LeftCosetSpace.mk _ v)
    rw [rationalQuotientIso_mk, quotientEval_mk V φ hφV, quotientEval_mk _ φ hφW]
    change φ (G.affinePointsTarget (G.innerIso a).hom _ v.val *
      (innerAdelicPoint F G a * x)) = φ (v.val * x)
    rw [affinePointsTarget_innerIso_hom]
    simpa only [mul_assoc, inv_mul_cancel_left] using hφa (v.val * x)

end Quotient

open AdelicSubgroupPoints in
omit [LocallyOfFiniteType G.X.hom] in
private theorem unipotent_rational_mem_parabolic (J : Set (characterLattice T))
    (v : adelicPoints F G (V[J])) (hv : v ∈ AdelicSubgroupPoints.rationalSubgroup F G (V[J])) :
    (v : Points) ∈ rationalImage F (p[J]) := by
  have hle : rationalImage F (u[J]) ≤ rationalImage F (p[J]) := by
    rw [← Standard.unipotentToParabolic_comp i ν J]
    exact rationalImage_comp_le _ _
  exact hle ((mem_rationalSubgroup_range_iff (u[J]) v).mp hv)

open AdelicSubgroupPoints in
private theorem compactSpace_radicalQuotient (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (V[J])) := by
  rw [(Standard.isRepresentedBy_unipotentHom i ν J).2]
  exact StandardConstantTerm.compactSpace_standardUnipotent F G i ν hG hi hν J hJ

section Standard

open AdelicSubgroupPoints

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
  (hJ : J ⊆ simpleRelativeRoots i ν)

include hG hi hν hJ in
/-- Local boundedness on the adelic group gives integrability on the compact radical quotient. -/
theorem hasConstantTerm_of_locallyBoundedInvariant {φ : Points → ℂ}
    (hφ : IsLocallyBoundedInvariant (parabolicRationalImage (F := F) (p[J])) φ)
    (x : Points) : HasConstantTerm F i ν J φ x := by
  have hφP : IsLocallyBoundedInvariant (rationalImage F (p[J])) φ := by
    rwa [← parabolicRationalImage_eq_rationalImage]
  let V := V[J]
  let U := adelicPoints F G V
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G V
  have hclosed : IsClosed (U : Set Points) := isClosed_adelicPoints_range F G (u[J])
  let : LocallyCompactSpace U := hclosed.locallyCompactSpace
  let mU := normalizedRationalQuotientHaarMeasure F G V
  let : CompactSpace (LeftCosetSpace Γ) := compactSpace_radicalQuotient hG hi hν J hJ
  let : IsProbabilityMeasure mU := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let f (n : U) : ℂ := φ ((n : Points) * x)
  have hfn : ∀ a ∈ Γ, ∀ n : U, f (a * n) = f n := by
    intro a ha n
    change φ (((a * n : U) : Points) * x) = φ ((n : Points) * x)
    rw [Subgroup.coe_mul, mul_assoc]
    exact hφP.2.2 _ (unipotent_rational_mem_parabolic J a ha) _
  have hf : Measurable f := hφ.1.comp (continuous_subtype_val.measurable.mul_const x)
  obtain ⟨C, hC, hcover⟩ := LeftCosetSpace.exists_isCompact_cover Γ
  obtain ⟨M, hM⟩ := hφ.2.1 _ (hC.image (continuous_subtype_val.mul_const x))
  change Integrable (fun q : LeftCosetSpace Γ => f q.out) mU
  have hfQ : Measurable (fun c : LeftCosetSpace Γ => f c.out) := by
    rw [RankinSelbergGlobal.Unfolding.out_eq_lift Γ f (fun a => hfn a a.2)]
    exact measurable_from_quotient.mpr hf
  refine Integrable.of_bound hfQ.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun c => ?_)
  obtain ⟨a, ha, hac⟩ := hcover c.out
  rw [← hfn a ha c.out]
  exact hM _ ⟨a * c.out, hac, rfl⟩

set_option maxHeartbeats 700000 in
include hG hi hν hJ in
/-- Integration along the radical preserves left invariance under the rational parabolic. -/
theorem constantTerm_rationalParabolic_mul {φ : Points → ℂ}
    (hφ : ∀ a ∈ rationalImage F (p[J]), ∀ x, φ (a * x) = φ x)
    (a : Points) (ha : a ∈ rationalImage F (p[J])) (x : Points) :
    constantTerm F i ν J φ (a * x) = constantTerm F i ν J φ x := by
  let V := V[J]
  let U := adelicPoints F G V
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G V
  let : IsClosed (U : Set Points) := isClosed_adelicPoints_range F G (u[J])
  let mU := normalizedRationalQuotientHaarMeasure F G V
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    compactSpace_radicalQuotient hG hi hν J hJ
  have hφV : ∀ v ∈ Γ, ∀ x, φ ((v : Points) * x) = φ x :=
    fun v hv => hφ _ (unipotent_rational_mem_parabolic J v hv)
  have hnorm : V.IsNormalizedBy (SubgroupFunctor.range (p[J])) := by
    dsimp only [V]
    rw [(Standard.isRepresentedBy_unipotentHom i ν J).2,
      (Standard.isRepresentedBy_parabolicHom i ν J).2]
    exact StandardConstantTerm.standardUnipotent_isNormalizedBy_standardParabolic i ν J
  obtain ⟨q, hq⟩ := (mem_rationalImage_iff (p[J]) a).mp ha
  let X := Over.mk (𝟙 (Spec (CommRingCat.of F)))
  let e : X ≅ (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)) :=
    Gm.affineTestIso _ _ (by exact (Spec.map_id (CommRingCat.of F)).symm)
  let y := e.hom ≫ q ≫ (p[J]).hom.hom
  have hy : innerAdelicPoint F G y = a := by
    rw [← hq, innerAdelicPoint_eq_rational, map_rational]
    congr 1
    let Z := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))
    have hZ : (Over.homMk Z.hom : Z ⟶ X) = e.inv := by
      apply Over.OverMorphism.ext
      change Z.hom = e.inv.left
      simpa only [show X.hom = 𝟙 _ from rfl, Category.comp_id] using (Over.w e.inv).symm
    change (Over.homMk Z.hom : Z ⟶ X) ≫ (e.hom ≫ q ≫ (p[J]).hom.hom) = _
    simp only [hZ, Iso.inv_hom_id_assoc]
    rfl
  have hyP : y ∈ (SubgroupFunctor.range (p[J])).carrier X :=
    SubgroupFunctor.mem_range.mpr ⟨e.hom ≫ q, Category.assoc _ _ _⟩
  have hV : V = SubgroupFunctor.comap (G.innerIso y).hom V :=
    (SubgroupFunctor.comap_innerIso_eq_of_isNormalizedBy hnorm hyP).symm
  change (∫ c, quotientEval V φ (a * x) c ∂mU) = ∫ c, quotientEval V φ x c ∂mU
  rw [← hy]
  exact integral_quotientEval_conj V V y hV φ hφV hφV (hy.symm ▸ hφ a ha) x

end Standard

end Langlands.Global.ArthurTruncation
