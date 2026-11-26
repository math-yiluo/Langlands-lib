import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthProof
import Langlands.Automorphic.GroupSchemeRationalAutomorphicRealization
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicRationalHeightReduction
import Langlands.Global.AdelicRelativeCuspidalRapidDecay
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicUniformDirectionalGrowth

/-! # Cuspidal decay on representatives of the norm-one quotient -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped CategoryTheory.MonObj Manifold ContDiff NNReal Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints AdelicSiegelFactors
  PositiveRealTorus RepresentationGrowth Langlands.LinearAlgebra.RationalSpan

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "H" => adelicHeight F G rho

/-- Each norm-one rational class has a representative on which the value times an
arbitrary prescribed power of the adelic height is uniformly bounded. -/
def HasRapidDecayOnNormOneRepresentatives (ψ : A → ℂ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : normOneSubgroup F G,
    ∃ q : RationalGroupPoints F G, ‖ψ (rational F G q * x.val)‖ *
      H (rational F G q * x.val) ^ m ≤ C

/-- An automorphic function with zero constant terms along all proper parabolics
has rapid decay on representatives of its norm-one rational quotient. -/
theorem hasRapidDecayOnNormOneRepresentatives_of_cuspidal
    (hG : IsConnectedReductive G) (hN : 0 < N) (hρ : IsClosedSubgroup rho)
    (hs : SmoothOfRelativeDimension d G.X.hom)
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    (hKinf : Langlands.CompactIwasawa.IsMaximalCompact Kinf) {ψ : A → ℂ}
    (hψ : IsAutomorphicFunctionOn F G hs (adelicDifferentialCommutator_of_smooth F G hs)
      (rationalSubgroup F G) Kinf rho ψ)
    (hcusp : ∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) (r : U ⟶ P)
      [IsAffine U.X.left] [IsClosedImmersion (r ≫ p).hom.hom.left],
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
      SubgroupFunctor.range p ≠ ⊤ → subgroupConstantTerm F (r ≫ p) ψ = 0) :
    HasRapidDecayOnNormOneRepresentatives rho ψ := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hs
  let hc := adelicDifferentialCommutator_of_smooth F G hs
  obtain ⟨f, hf, heval⟩ := rationalAutomorphicRealization rho hs hc Kinf ψ hψ
  have hg := adelicAutomorphicUniformGrowth F G Kinf rho hs hG hρ hKinf hN f hf
  obtain ⟨R, hR⟩ := (hasAdelicUniformModerateGrowth_iff F G rho hs hc hN f).mp hg
  have hD (s : List (smoothModel F d)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖adelicIteratedDirectionalValue hs s ψ x‖ ≤ C * H x ^ (R : ℝ) := by
    obtain ⟨C, hC, hbound⟩ := hR (adelicDirectionalWordEnveloping hs s)
    refine ⟨C, hC, fun x => ?_⟩
    simpa only [evaluate_adelicDirectionalWordEnveloping hs hc s f, heval, Real.rpow_natCast]
      using hbound x
  have hslice (b : FiniteAdelicGroupPoints F G) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun y => ψ (pair F G y b)) := by
    rw [← heval]
    exact ((mem_finitePlotSmoothRationalSubrepresentation_iff_contMDiff F G hs f.val).mp
      f.property).1 b
  obtain ⟨L, hL, hlevel⟩ := hψ.2.1.2.2
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, ht₀, _⟩ := hS.2.2.2.2.2.2.2.1
    exact ht₀.1.1
  let fam := StandardParabolicFamily.ofMaximalSplitTorus hG i hS.1 ν hS.2.1
  let B₀ : StandardIndex F G fam.i fam.ν := ⟨∅, empty_subset _⟩
  let Δ := simpleRelativeRoots fam.i fam.ν
  have hspan : ratSpan (((fun α : characterLattice fam.T => j ≫ α) '' Δ) ∪ ∅) = ⊤ := by
    rw [Set.union_empty]
    exact ratSpan_restrict_simpleRelativeRoots_eq_top
      relativeRootNegation relativeCharacterRootComplement hG hS
  have htop : SubgroupFunctor.range (fam.p fam.top) = ⊤ := by
    rw [(fam.isCompatible fam.top).parabolic_eq]
    exact (standardParabolicEndpoints F G hG T i hS.1 ν hS.2.1).2.2.1
  have hproper : fam.IsCuspidalAlong fam.top ψ := by
    intro J hJ
    refine hcusp (fam.P J) (fam.U J) (fam.p J) (fam.iU J)
      (fam.isCompatible J).parabolic (fam.isUnipotentRadical J) ?_
    intro heq
    have hle : fam.top ≤ J := (fam.le_iff_range_le fam.top J).2 (htop.trans heq.symm).le
    exact (not_le_of_gt hJ) hle
  have hU : ∀ u : AdelicGroupPoints F (fam.U fam.top), ∀ x,
      ψ (map F (fam.U fam.top) G (fam.iU fam.top ≫ fam.p fam.top) u * x) = ψ x := by
    intro u x
    let r := fam.iU fam.top ≫ fam.p fam.top
    have hbot : SubgroupFunctor.range r = ⊥ := (fam.range_radical_eq_standardUnipotent
      fam.top).trans (standardUnipotent_simple_eq_bot i ν)
    have hmem : map F (fam.U fam.top) G r u ∈
        (SubgroupFunctor.range r).carrier _ := ⟨u, rfl⟩
    rw [hbot] at hmem
    rw [show map F (fam.U fam.top) G r u = 1 from hmem, one_mul]
  obtain ⟨K, _, W, hKc, _, _, _, _, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F G hG T i ν T₀ j hS
  obtain ⟨C, t, rfl, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F G hG T i ν T₀ j hS K hKc W hW hW1 hcov
  let D := canonicalStandardFactors F G T i ν
  let Ω := compactPrefix F G T i ν D C
  let K' : Set A := (C.compactSubgroup : Set A) * W
  have hΩ : IsCompact Ω := (C.compact_omegaN.image (map F D.unipotent G
    D.unipotentInclusion).continuous).mul (C.compact_omegaM.image
      ((map F D.levi G D.leviInclusion).continuous.comp continuous_subtype_val))
  have hK' : IsCompact K' := C.compact_compactSubgroup.mul hW.isCompact
  have hΩB : Ω ⊆ ((map F (fam.P B₀) G (fam.p B₀)).toMonoidHom.range : Set A) := by
    rintro _ ⟨_, ⟨n, _, rfl⟩, _, ⟨m, _, rfl⟩, rfl⟩
    exact (standardParabolicImage F G T i ν).mul_mem
      (standardUnipotentImage_le_parabolic F G T i ν ⟨n, rfl⟩)
      (standardLeviImage_le_parabolic F G T i ν ⟨m.val, rfl⟩)
  let Yf := (finite F G '' Ω) * (finite F G '' K')
  have hYf : IsCompact Yf := (hΩ.image (finite F G).continuous).mul
    (hK'.image (finite F G).continuous)
  have hRat r (hr : r ∈ rationalImage F (fam.p B₀)) (x : A) : ψ (r * x) = ψ x :=
    hψ.1 r (rationalImage_le_rationalSubgroup _ hr) x
  intro m
  obtain ⟨B, hB, hdecay⟩ := fam.adelicRelativeCuspidalRapidDecay j hs rho hT₀ hN
    fam.top ∅ hspan t 0 le_rfl Ω K' hΩ hK' hΩB Yf hYf L hL Unit (fun _ => ψ)
    (fun _ => 1) (fun _ => zero_le_one) (fun _ => hψ.2.1.1) (fun _ => hslice)
    (fun _ => hRat) (fun _ => hU) (fun _ => hlevel) (fun _ => hproper)
    (R : ℝ) (Nat.cast_nonneg _) (fun s => by
      obtain ⟨c, hc, h⟩ := hD s
      exact ⟨c, hc, fun _ x => by simpa only [mul_one] using h x⟩) m
  refine ⟨B, hB, fun x => ?_⟩
  obtain ⟨q, hq⟩ := hcover x
  obtain ⟨g₀, hg₀, w, hw, hgw⟩ := hq
  obtain ⟨n, hn, y, hy, a, ha, k, hk, heq⟩ :=
    (mem_productSet_iff F G T i ν D C T₀ j _ g₀).mp hg₀
  let p := map F D.unipotent G D.unipotentInclusion n * map F D.levi G D.leviInclusion y.val
  have hp : p ∈ Ω := ⟨_, ⟨n, hn, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  have hkw : k * w ∈ K' := ⟨k, hk, w, hw, rfl⟩
  have hfin : finite F G (p * positiveMap F G T i T₀ j a * (k * w)) ∈ Yf := by
    rw [map_mul, map_mul, finite_positiveMap F G T i T₀ j hT₀ a, mul_one]
    exact ⟨_, ⟨p, hp, rfl⟩, _, ⟨k * w, hkw, rfl⟩, rfl⟩
  have hb := hdecay () p hp a ha (by simp) (by simp [StandardParabolicFamily.top])
    (k * w) hkw hfin
  have hx : p * positiveMap F G T i T₀ j a * (k * w) = rational F G q * x.val := by
    rw [← mul_assoc]
    change (map F D.unipotent G D.unipotentInclusion n * map F D.levi G D.leviInclusion y.val *
      positiveMap F G T i T₀ j a * k) * w = _
    rw [heq]
    exact hgw
  refine ⟨q, ?_⟩
  rw [← hx]
  change ‖ψ (p * positiveMap F G T i T₀ j a * (k * w))‖ *
    H (p * positiveMap F G T i T₀ j a * (k * w)) ^ m ≤ B * 1 at hb
  simpa only [mul_one] using hb

end Langlands.Global
