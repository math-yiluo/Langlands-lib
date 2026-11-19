import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviDominantReduction
import Langlands.Representation.Jacquet.StandardCasselmanTensorDepth

/-! # Uniform constant-term thresholds on the full minimal Levi -/

noncomputable section

universe u uV uκ

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

private theorem exists_nhds_one_conj_mem {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] {Q : Set X} (hQ : IsCompact Q) (H : OpenSubgroup X) :
    ∃ U ∈ 𝓝 (1 : X), ∀ x ∈ Q, ∀ k ∈ U, x⁻¹ * k * x ∈ H := by
  let T : Set (X × X) := {p | p.1⁻¹ * p.2 * p.1 ∈ H}
  have hT : IsOpen T := H.isOpen.preimage ((continuous_fst.inv.mul continuous_snd).mul continuous_fst)
  have hmem : T ∈ (𝓝ˢ Q) ×ˢ 𝓝 (1 : X) := hQ.mem_nhdsSet_prod_of_forall fun x _ => by
    rw [← nhds_prod_eq]
    exact hT.mem_nhds (show x⁻¹ * 1 * x ∈ H by simp)
  obtain ⟨O, hO, U, hU, hsub⟩ := Filter.mem_prod_iff.mp hmem
  refine ⟨U, hU, fun x hx k hk => ?_⟩
  change (x, k) ∈ T
  exact hsub ⟨mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hO x hx), hk⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A A₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

private theorem finite_image_rationalMinimalH0 {Q : Set (standardLeviPoints i ν ∅)}
    (hQ : IsCompact Q) : (rationalMinimalH0 hG hi hν '' Q).Finite := by
  let M := Standard.leviScheme i ν ∅
  let j := Standard.leviHom i ν ∅
  have hj : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_leviHom i ν ∅
  let : IsAffine M.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : LocallyOfFiniteType M.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  let e := standardLeviRationalPointsHomeomorph i ν ∅ j
    (Standard.isRepresentedBy_leviHom i ν ∅) hj
  let p := rationalValuationImageProjection M ∘ e.symm
  have hp : Continuous p := (continuous_rationalValuationImageProjection M).comp e.symm.continuous
  let s := Standard.leviTorusHom i ν ∅
  let h := minimalLevi_restrictionEvaluation_bijective hG hi hν
  let eVal := BruhatTits.Cartan.centralizerValuationImageEquiv s h
  let toH : rationalDiscreteValuationImage M → RealTorusSpace.V S := fun z => (eVal.symm z).val.toAdd
  apply ((hQ.image hp).finite_of_discrete.image toH).subset
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨p m, ⟨m, hm, rfl⟩, ?_⟩
  have he : e.toMulEquiv = Standard.leviPointsEquiv i ν ∅ :=
    standardLeviRationalPointsHomeomorph_toMulEquiv i ν ∅ j
      (Standard.isRepresentedBy_leviHom i ν ∅) hj
  have hes : e.symm m = (Standard.leviPointsEquiv i ν ∅).symm m := by
    change e.toMulEquiv.symm m = _
    rw [he]
  let z : BruhatTits.Cartan.centralizerValuationImage s h :=
    ⟨BruhatTits.Cartan.centralizerValuation s h (e.symm m), e.symm m, rfl⟩
  have hz : eVal z = p m := BruhatTits.Cartan.centralizerValuationImageEquiv_apply s h (e.symm m)
  rw [← hz]
  change (eVal.symm (eVal z)).val.toAdd = _
  rw [MulEquiv.symm_apply_apply]
  change (BruhatTits.Cartan.centralizerValuation s h (e.symm m)).toAdd =
    rationalMinimalH0 hG hi hν m
  rw [hes]
  rfl

variable {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)

/-- A family of coefficients satisfies the normalized constant-term identity at
one common depth on the full closed chamber of the actual minimal Levi. -/
def HasUniformMinimalLeviConstantTermThreshold {κ : Type uκ}
    (f : κ → rationalPoints G → ℂ) : Prop :=
  ∃ t > 0, ∀ ω, ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν J t,
    f ω (m : rationalPoints G) =
      standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
        standardConstantTerm hA (f ω) (minimalLeviInclusion hG hi hν J m)

include hi in
private theorem standardConstantTerm_mul_left_right {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) {f : rationalPoints G → ℂ}
    (hf : HasStandardConstantTerm hA f) (l r : standardLeviPoints i ν J) :
    standardConstantTerm hA (fun x => f ((l : rationalPoints G) * x * (r : rationalPoints G))) =
      fun m => standardHalfModulus i ν J l * standardHalfModulus i ν J r *
        standardConstantTerm hA f (l * m * r) := by
  let f₁ := fun x => f ((l : rationalPoints G) * x)
  have h₁ : HasStandardConstantTerm hA f₁ :=
    ⟨_, (isRightFinite_comp_mul_left' (hf.isRightFinite hA) l).smul _,
      (hf.isStandardConstantTerm hA).mul_left hA l⟩
  have hEq : (fun x => f ((l : rationalPoints G) * x * (r : rationalPoints G))) =
      fun x => f₁ (x * (r : rationalPoints G)) := by
    funext x
    exact congrArg f (mul_assoc _ _ _)
  rw [hEq, standardConstantTerm_mul_right hi hζ hA h₁,
    standardConstantTerm_mul_left hi hζ hA hf]
  funext m
  dsimp only
  rw [← mul_assoc l]
  ring

variable {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ)
  (hJ : J ⊆ simpleRelativeRoots i ν)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν J q L)
  {q₀ : A₀.toGrp ⟶ S.toGrp} (hA₀ : IsCompatibleStandardSplitComponent i ν ∅ A₀ q₀)
  (hmem₀ : ∀ L ∈ B, StandardParabolicBasisMember i ν ∅ q₀ L)

include hζ hJ hB hmem hA₀ hmem₀ in
set_option maxHeartbeats 1400000 in
/-- Uniform fixed dimensions and one common invariance subgroup give a threshold
on the full minimal Levi, using compact dominant reduction. -/
theorem hasUniformMinimalLeviConstantTermThreshold_of_fixedRanks
    (hred : HasCompactDominantMinimalLeviReduction hG hi hν)
    {κ : Type uκ} (ρ : κ → SmoothRep.{0, u, uV} ℂ (rationalPoints G))
    (hρ : ∀ ω, (ρ ω).IsAdmissible) (T : ∀ ω, CoefficientTensor (ρ ω))
    (H : OpenSubgroup (rationalPoints G))
    (hbi : ∀ ω (k l : H) g,
      coefficientTensorMap (ρ ω) (T ω) ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        coefficientTensorMap (ρ ω) (T ω) g)
    (hrank : ∀ L ∈ B, ∃ d : ℕ, ∀ ω, Module.finrank ℂ (fixedVectors (ρ ω).representation L) ≤ d) :
    HasUniformMinimalLeviConstantTermThreshold hG hi hν hA
      (fun ω g => coefficientTensorMap (ρ ω) (T ω) g) := by
  obtain ⟨Q, hQ, hreduce⟩ := hred
  obtain ⟨c, hdepth⟩ := exists_standardCasselman_boundedDepth.{u, uV}
    hG hi hν hJ hζ hB hA hmem hA₀ hmem₀
  let QG := ((↑) : standardLeviPoints i ν ∅ → rationalPoints G) '' Q ∪
    (fun k : standardLeviPoints i ν ∅ => (k : rationalPoints G)⁻¹) '' Q
  have hQG : IsCompact QG :=
    (hQ.image continuous_subtype_val).union (hQ.image continuous_subtype_val.inv)
  obtain ⟨U, hU, hconj⟩ := exists_nhds_one_conj_mem hQG H
  obtain ⟨L, hL, hLU⟩ := hB.2.mem_iff.mp hU
  let L' := basisOpenSubgroup hB hL
  obtain ⟨d, hd⟩ := hrank L hL
  let H0 := rationalMinimalH0 hG hi hν
  have hfin := finite_image_rationalMinimalH0 hG hi hν hQ
  let E := (simpleRelativeRoots i ν ×ˢ (H0 '' Q)) ×ˢ (H0 '' Q)
  let s := fun p : (characterLattice S × RealTorusSpace.V S) × RealTorusSpace.V S =>
    RealTorusSpace.eval S p.1.1 (p.1.2 + p.2)
  have hE : (s '' E).Finite :=
    (((hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).prod hfin).prod hfin).image s
  obtain ⟨R, hR⟩ := hE.bddAbove
  refine ⟨(d : ℝ) * c + max R 0 + 1, by positivity, fun ω m hm => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, y, hy, hmeq⟩ := hreduce m hm.1
  have hdeep : ∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
      (d : ℤ) * c ≤ latticePairing S α y := by
    intro α hα hαJ
    have ht := hm.2 α ⟨hα, hαJ⟩
    rw [hmeq, rationalMinimalH0_mul, rationalMinimalH0_mul,
      rationalMinimalH0_minimalLeviUniformizer, map_add, map_add,
      RealTorusSpace.eval_tmul, one_mul] at ht
    have hshift : RealTorusSpace.eval S α (H0 k₁ + H0 k₂) ≤ R :=
      hR ⟨((α, H0 k₁), H0 k₂), ⟨⟨hα, ⟨k₁, hk₁, rfl⟩⟩, ⟨k₂, hk₂, rfl⟩⟩, rfl⟩
    rw [map_add] at hshift
    have hle : (d : ℝ) * c ≤ (latticePairing S α y : ℝ) := by
      have hmax : R ≤ max R 0 := le_max_left _ _
      linarith
    exact_mod_cast hle
  let incl := minimalLeviInclusion hG hi hν J
  let a := incl (minimalLeviUniformizer (i := i) (ν := ν) y)
  let l := incl k₁
  let r := incl k₂
  let f := fun g => coefficientTensorMap (ρ ω) (T ω) g
  let T' := coefficientTensorAction (ρ ω)
    ((k₂ : rationalPoints G), (k₁ : rationalPoints G)⁻¹) (T ω)
  have hf' : (fun g => coefficientTensorMap (ρ ω) T' g) =
      fun g => f ((l : rationalPoints G) * g * (r : rationalPoints G)) := by
    funext g
    dsimp only [T', f]
    rw [coefficientTensorMap_action]
    simp only [inv_inv, l, r, incl, coe_minimalLeviInclusion]
  have hlfix (k : L') : (k₁ : rationalPoints G) * k * (k₁ : rationalPoints G)⁻¹ ∈ H := by
    have h := hconj ((k₁ : rationalPoints G)⁻¹) (Or.inr ⟨k₁, hk₁, rfl⟩) k (hLU k.property)
    simpa only [inv_inv] using h
  have hrfix (k : L') : (k₂ : rationalPoints G)⁻¹ * k * (k₂ : rationalPoints G) ∈ H :=
    hconj (k₂ : rationalPoints G) (Or.inl ⟨k₂, hk₂, rfl⟩) k (hLU k.property)
  have hbi' (k k' : L') (g : rationalPoints G) :
      coefficientTensorMap (ρ ω) T' ((k : rationalPoints G) * g * (k' : rationalPoints G)) =
        coefficientTensorMap (ρ ω) T' g := by
    change (fun x => coefficientTensorMap (ρ ω) T' x) (_ * g * _) =
      (fun x => coefficientTensorMap (ρ ω) T' x) g
    rw [hf']
    dsimp only
    have heq : (l : rationalPoints G) * ((k : rationalPoints G) * g * (k' : rationalPoints G)) *
          (r : rationalPoints G) =
        ((k₁ : rationalPoints G) * k * (k₁ : rationalPoints G)⁻¹) *
          ((l : rationalPoints G) * g * (r : rationalPoints G)) *
          ((k₂ : rationalPoints G)⁻¹ * k' * (k₂ : rationalPoints G)) := by
      simp only [l, r, incl, coe_minimalLeviInclusion]
      group
    rw [heq]
    exact hbi ω ⟨_, hlfix k⟩ ⟨_, hrfix k'⟩ _
  have ha : (a : rationalPoints G) = Aubert.General.uniformizerPowers i (.ofAdd y) := by
    simp only [a, incl, coe_minimalLeviInclusion, coe_minimalLeviUniformizer]
  have hlat := hdepth.coefficientTensorMap_eq_mul_constantTerm hL (ρ ω) (hρ ω) (hd ω) T'
    hbi' y hy hdeep a ha
  change (fun g => coefficientTensorMap (ρ ω) T' g) (a : rationalPoints G) = _ at hlat
  rw [hf'] at hlat
  have hfmem : f ∈ coefficientFunctionSpace (ρ ω) := by
    rw [coefficientFunctionSpace_eq_map]
    exact ⟨_, ⟨T ω, rfl⟩, rfl⟩
  have hCT := (standardConstantTerm_spec hG hi hν hζ hB hA hmem
    (ρ ω).representation (hρ ω) hfmem).1
  rw [standardConstantTerm_mul_left_right hi hA hζ hCT l r] at hlat
  have hm' : incl m = l * a * r := by
    rw [hmeq, map_mul, map_mul]
  have hmG : (m : rationalPoints G) = (l : rationalPoints G) * a * r := by
    rw [← coe_minimalLeviInclusion hG hi hν J m]
    change (incl m : rationalPoints G) = _
    rw [hm']
    rfl
  change f (m : rationalPoints G) =
    standardHalfModulus i ν J (incl m) * standardConstantTerm hA f (incl m)
  calc
    f (m : rationalPoints G) = f ((l : rationalPoints G) * a * r) := congrArg f hmG
    _ = standardHalfModulus i ν J a *
        (standardHalfModulus i ν J l * standardHalfModulus i ν J r *
          standardConstantTerm hA f (l * a * r)) := hlat
    _ = _ := by
      rw [hm', standardHalfModulus_mul, standardHalfModulus_mul]
      ring

end Langlands.HarishChandraSchwartz
