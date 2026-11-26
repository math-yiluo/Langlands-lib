import Langlands.Automorphic.GroupSchemeSmoothConstantTermSlice
import Langlands.Analysis.FiniteSubspaceInterpolation
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicEisensteinGrowthBound
import Langlands.Global.AdelicRepresentationHeightExhaustion
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Global.EisensteinConstantTerm.Reduction
import Langlands.GroupScheme.Dynamic.SubgroupMaximality

/-! # Transfer of fixed profiles and infinitesimal equations to a constant term -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme AdelicGroupPoints InfiniteAdelicGroupPoints
  RepresentationGrowth AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P U M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom] (p : P ⟶ G) (j : U ⟶ P) [IsClosedImmersion (j ≫ p).hom.hom.left]
  (hU : LeviSubgroup.IsGeometricUnipotentRadical j)

local notation "A" => AdelicGroupPoints F G
local notation "V" => FinitePlotSmoothRationalFunctions F G
local notation "Nrad" => SubgroupFunctor.range (j ≫ p)
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G Nrad
local notation "Unip" => AdelicSubgroupPoints.adelicPoints F G Nrad
local notation "mu" => normalizedRationalQuotientHaarMeasure F G Nrad

private local instance : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
private local instance : IsClosed (Unip : Set A) := isClosed_adelicPoints_range F G (j ≫ p)
private local instance : BorelSpace Q := rationalQuotientBorelSpace F G Nrad

include hU in
omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsClosedImmersion (j ≫ p).hom.hom.left] in
private theorem compact_radicalQuotient : CompactSpace Q :=
  compactSpace_rationalQuotient_range_unipotent F (j ≫ p)
    hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent

/-- The normalized constant term along the actual radical is a complex linear map on the
finite plot-smooth rational carrier. -/
def parabolicConstantTermLinear : V →ₗ[ℂ] (A → ℂ) :=
  letI := compact_radicalQuotient p j hU
  letI : IsProbabilityMeasure mu := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G Nrad
  (compactConstantTermLinearMap F G Nrad mu).comp
    (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype

theorem parabolicConstantTermLinear_apply (f : V) (g : A) :
    parabolicConstantTermLinear p j hU f g = subgroupConstantTerm F (j ≫ p) (evaluate F G f.val) g :=
  (subgroupConstantTerm_eq_continuousConstantTerm (j ≫ p) f.val g).symm

private theorem parabolicConstantTermLinear_invariant (l : M ⟶ P) (f : V) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p j l) (parabolicConstantTermLinear p j hU f) := by
  let := compact_radicalQuotient p j hU
  let CT := parabolicConstantTermLinear p j hU f
  let Fix : Subgroup A :=
    { carrier := {x | ∀ g, CT (x * g) = CT g}
      one_mem' := fun g => congrArg CT (one_mul g)
      mul_mem' := by
        intro x y hx hy g
        rw [mul_assoc, hx, hy]
      inv_mem' := by
        intro x hx g
        have h := hx (x⁻¹ * g)
        rwa [mul_inv_cancel_left, eq_comm] at h }
  have hNorm := Dynamic.range_comp_isNormalizedBy_of_isNormal j p hU.1.isNormal
  have hle : parabolicQuotientSubgroup F p j l ≤ Fix := by
    apply sup_le
    · intro x hx g
      exact normalizedConstantTerm_subgroup_mul F G Nrad f.val ⟨x, hx⟩ g
    · rintro _ ⟨r, rfl⟩ g
      let r' : AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range p) :=
        ⟨M.affinePointsTarget (l ≫ p) (CommAlgCat.of F F) r,
          ⟨M.affinePointsTarget l (CommAlgCat.of F F) r, by
            change (r ≫ l.hom.hom) ≫ p.hom.hom = r ≫ (l ≫ p).hom.hom
            rw [Grp.comp_hom_hom, Category.assoc]⟩⟩
      have hr : (AdelicSubgroupPoints.rational F G (SubgroupFunctor.range p) r').val =
          map F M G (l ≫ p) (AdelicGroupPoints.rational F M r) := by
        rw [map_rational]
        rfl
      change CT (map F M G (l ≫ p) (AdelicGroupPoints.rational F M r) * g) = CT g
      rw [← hr]
      exact normalizedConstantTerm_rationalNormalizer_mul F G Nrad hNorm r' f.val g
  exact fun x hx => hle hx

private theorem hasModerateGrowth_parabolicConstantTermLinear
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (f : V)
    (hGrow : HasModerateGrowthFunction F G rho (evaluate F G f.val)) :
    HasModerateGrowthFunction F G rho (parabolicConstantTermLinear p j hU f) := by
  let := compact_radicalQuotient p j hU
  let : IsProbabilityMeasure mu := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G Nrad
  let : LocallyCompactSpace Unip := (show IsClosed (Unip : Set A) from inferInstance).locallyCompactSpace
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G Nrad
  obtain ⟨S, hS, hSrep⟩ := EisensteinConstantTerm.exists_isCompact_mul_mem Γ
  obtain ⟨B, hB⟩ := exists_nat_adelicHeight_bound_of_isCompact F G rho hN
    (hS.image (continuous_subtype_val : Continuous fun n : Unip => (n : A)))
  obtain ⟨r, hr, hBound⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height hGrow
  obtain ⟨C, hC, hF⟩ := hBound ({1} : Set A) isCompact_singleton
  let D : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hD : 0 < D := pow_pos (Nat.cast_pos.mpr hN) _
  let B' : ℝ := 1 + B
  have hB' : 0 < B' := by positivity
  refine ⟨C * B' ^ r * D ^ r,
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hB' _)) (Real.rpow_pos_of_pos hD _), r, fun g => ?_⟩
  change ‖∫ x : Q, constantTermIntegrand F G Nrad f.val g x ∂mu‖ ≤ _
  calc
    _ ≤ C * B' ^ r * adelicHeight F G rho g ^ r := by
      refine (norm_integral_le_of_norm_le_const (C := C * B' ^ r * adelicHeight F G rho g ^ r)
        (Filter.Eventually.of_forall fun x => ?_)).trans_eq (by simp)
      obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective Γ x
      obtain ⟨q, hq, s, hs, hqs⟩ := hSrep y
      have hsame : LeftCosetSpace.mk Γ y = LeftCosetSpace.mk Γ s := by
        rw [hqs]
        exact LeftCosetSpace.mk_subgroup_mul Γ ⟨q, hq⟩ s
      rw [hsame, constantTermIntegrand_mk]
      have hSB : adelicHeight F G rho (s : A) ≤ B' :=
        (hB ⟨s, hs, rfl⟩).trans (le_add_of_nonneg_left zero_le_one)
      have h0 (g : A) : 0 ≤ adelicHeight F G rho g := zero_le_one.trans (one_le_adelicHeight F G rho hN g)
      have hg := hF ((s : A) * g) 1 (Set.mem_singleton 1)
      rw [mul_one, adelicHeightAtLeastOne_eq hN] at hg
      refine hg.trans ?_
      rw [mul_assoc C, ← Real.mul_rpow hB'.le (h0 g)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (h0 _)
        ((adelicHeight_mul_le F G rho hN _ _).trans
          (mul_le_mul_of_nonneg_right hSB (h0 g))) hr) hC.le
    _ = _ := by
      rw [adelicHeight_eq_scalar_mul_sourceNorm,
        Real.mul_rpow hD.le (adelicSourceNorm_pos F G rho hN g).le]
      ring

/-- All right profiles of the constant term lie in the same space as the original profiles. -/
private theorem compactProfile_parabolicConstantTermLinear
    (H : Subgroup (InfiniteAdelicGroupPoints F G)) (E : Submodule ℂ (H → ℂ))
    [FiniteDimensional ℂ E] (f : V)
    (hE : ∀ g : A, (fun k : H => evaluate F G f.val (g * ofInfinite F G k.val)) ∈ E)
    (g : A) : (fun k : H => parabolicConstantTermLinear p j hU f (g * ofInfinite F G k.val)) ∈ E := by
  classical
  let := compact_radicalQuotient p j hU
  let : IsProbabilityMeasure mu := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G Nrad
  let profile (q : Q) (k : H) := constantTermIntegrand F G Nrad f.val (g * ofInfinite F G k.val) q
  obtain ⟨n, nodes, w, hw, hInterp⟩ := Langlands.Analysis.finiteSubspaceInterpolation H Unit (fun _ => E)
  have hq (q : Q) : profile q ∈ E := by
    induction q using Quotient.inductionOn with
    | _ a =>
      have heq : profile (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G Nrad) a) =
          fun k : H => evaluate F G f.val (((a : Unip) : A) * g * ofInfinite F G k.val) := by
        funext k
        rw [show profile (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G Nrad) a) k =
          constantTermIntegrand F G Nrad f.val (g * ofInfinite F G k.val)
            (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G Nrad) a) from rfl,
          constantTermIntegrand_mk, mul_assoc]
      change profile (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G Nrad) a) ∈ E
      rw [heq]
      exact hE (_ * g)
  have hRec (q : Q) (k : H) : profile q k = ∑ i, w () i k * profile q (nodes i) := by
    have h : profile q ∈ ⨆ (_ : Unit), E := (le_iSup (fun _ : Unit => E) ()) (hq q)
    simpa using hInterp (profile q) h k
  have hInt (k : H) : Integrable (fun q => profile q k) mu :=
    hasConvergentConstantTerm_of_compact F G Nrad mu f.val (g * ofInfinite F G k.val)
  let c (i : Fin n) := ∫ q : Q, profile q (nodes i) ∂mu
  have hsum : (fun k : H => parabolicConstantTermLinear p j hU f (g * ofInfinite F G k.val)) =
      ∑ i, c i • w () i := by
    funext k
    change (∫ q : Q, profile q k ∂mu) = (∑ i, c i • w () i) k
    simp_rw [hRec _ k]
    rw [integral_finsetSum _ (fun i _ => (hInt (nodes i)).const_mul _)]
    simp only [integral_const_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, mul_comm]
  rw [hsum]
  exact E.sum_mem fun i _ => E.smul_mem _ (hw () i)

set_option maxHeartbeats 950000 in
/-- The unnormalized parabolic constant term preserves the prescribed finite level, growth,
infinitesimal equations and compact profiles, on the actual unipotent and rational Levi quotient. -/
theorem parabolicConstantTermLinear_fixedProfile
    (l : M ⟶ P) {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (H : Subgroup (InfiniteAdelicGroupPoints F G))
    (J : Ideal (AdelicEnvelopingCenter F G hsmooth)) (E : Submodule ℂ (H → ℂ))
    [FiniteDimensional ℂ E] (f : V)
    (hGrow : HasModerateGrowthFunction F G rho (evaluate F G f.val))
    (hFix : f.val ∈ levelSubmodule F G L.toSubgroup)
    (hAnn : ∀ z ∈ J, adelicCenterAction F G hsmooth hcalc z f = 0)
    (hProf : ∀ g : A, (fun k : H => evaluate F G f.val (g * ofInfinite F G k.val)) ∈ E) :
    let t := parabolicConstantTermLinear p j hU f
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p j l) t ∧
    IsAdelicSmoothFunction F G t ∧ HasModerateGrowthFunction F G rho t ∧
    (∀ b ∈ L, ∀ g, t (g * ofFinite F G b) = t g) ∧
    (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ hf : functionInfiniteSlice F G t b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G t b, hf⟩ = 0) ∧
    ∀ g, (fun k : H => t (g * ofInfinite F G k.val)) ∈ E := by
  let := compact_radicalQuotient p j hU
  let t := parabolicConstantTermLinear p j hU f
  have hcont : Continuous t := by
    rw [show t = subgroupConstantTerm F (j ≫ p) (evaluate F G f.val) from
      funext (parabolicConstantTermLinear_apply p j hU f)]
    exact continuous_subgroupConstantTerm (j ≫ p) f.val
  let Slice := plotSmoothConstantTermSlice (j ≫ p) hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent hsmooth
  have hSlice (b : FiniteAdelicGroupPoints F G) : functionInfiniteSlice F G t b = (Slice b f).val :=
    funext fun a => (parabolicConstantTermLinear_apply p j hU f _).trans
      (plotSmoothConstantTermSlice_apply (j ≫ p) hU.1.smooth hU.1.connectedSpace hU.1.isUnipotent hsmooth b f a).symm
  have hLevel : ∀ b ∈ L, ∀ g : A, t (g * ofFinite F G b) = t g := by
    intro b hb g
    change constantTerm F G Nrad mu f.val (g * ofFinite F G b) = constantTerm F G Nrad mu f.val g
    unfold constantTerm
    rw [← constantTermIntegrand_rightAction, hFix ⟨b, hb⟩]
  refine ⟨parabolicConstantTermLinear_invariant p j hU l f,
    ⟨hcont, fun b => (hSlice b).symm ▸ (Slice b f).property, L.toSubgroup, L.isOpen, hLevel⟩,
    hasModerateGrowth_parabolicConstantTermLinear p j hU rho hN f hGrow, hLevel, ?_,
    compactProfile_parabolicConstantTermLinear p j hU H E f hProf⟩
  intro z hz b hf
  have he : (⟨functionInfiniteSlice F G t b, hf⟩ : InfinitePlotSmoothFunctions F G) = Slice b f :=
    Subtype.ext (hSlice b)
  rw [he]
  change plotSmoothEnvelopingAction F G hsmooth hcalc z.val (Slice b f) = 0
  rw [show Slice b = plotSmoothConstantTermSlice (j ≫ p) hU.1.smooth hU.1.connectedSpace
    hU.1.isUnipotent hsmooth b from rfl, ← plotSmoothConstantTermSlice_enveloping,
    show adelicEnvelopingAction F G hsmooth hcalc z.val f = 0 from hAnn z hz, map_zero]

end Langlands.Automorphic.GroupSchemeFunctions
