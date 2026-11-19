import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLeviLowerComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviDominantReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi

/-! # Ambient Xi controls the normalized Levi Xi on the full minimal chamber -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

private theorem exists_open_neighborhood_conjugated_into
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Q U : Set G} (hQ : IsCompact Q) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ x ∈ Q, ∀ v ∈ V, x⁻¹ * v * x ∈ U := by
  let f : G × G → G := fun p => p.2⁻¹ * p.1 * p.2
  have hf : Continuous f := (continuous_snd.inv.mul continuous_fst).mul continuous_snd
  have hprod : ({1} : Set G) ×ˢ Q ⊆ f ⁻¹' U := by
    rintro ⟨v, x⟩ ⟨hv, _⟩
    change v = 1 at hv
    simpa [f, hv] using h1
  obtain ⟨V, W, hV, _, h1V, hQW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hQ (hU.preimage hf) hprod
  refine ⟨V, hV, h1V (Set.mem_singleton 1), fun x hx v hv => ?_⟩
  change (v, x) ∈ f ⁻¹' U
  exact hVW ⟨hv, hQW hx⟩

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
  (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

set_option hygiene false in
local notation "incM" => minimalLeviInclusion hG hi hν J

/-- The half-modulus-scaled Levi Xi is controlled by ambient Xi on the full
actual minimal-Levi closed chamber. -/
def HasRationalLeviXiHalfModulusComparison : Prop :=
  ∃ C > 0, ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
    ‖standardHalfModulus i ν J (incM m)‖ * rationalLeviXi hKc hMK (incM m) ≤
      C * rationalXi hKc hPK (m : rationalPoints G)

include hJ hKo in
/-- Compact dominant reduction and the minimal standard basis give a common
open subgroup on which the double spherical integrand can be integrated
without loss of height powers. -/
theorem hasRationalLeviXiHalfModulusComparison_of_basis
    {K₀ : Subgroup (rationalPoints G)} (hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K₀)
    (hcover : StandardLeviCartanCovering F i ν ∅ K₀) :
    HasRationalLeviXiHalfModulusComparison hG hi hν hKc hPK hMK := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  let h := isSemidirectDecomposition_standard hG hi hν hJ
  have hmP := continuous_projection_standard hG hi hν hJ h
  obtain ⟨Q, hQ, hreduce⟩ := hasCompactDominantMinimalLeviReduction_of_cartanCovering
    hG hi hν hK₀ hcover
  let QG := ((↑) : standardLeviPoints i ν ∅ → rationalPoints G) '' Q
  have hQG : IsCompact QG := hQ.image continuous_subtype_val
  obtain ⟨B, hB, hstd⟩ := hbasis
  obtain ⟨_, A₀, q₀, hA₀, hmembers⟩ := hstd ∅ (Set.empty_subset _)
  obtain ⟨V₂, hV₂o, hV₂one, hV₂⟩ := exists_open_neighborhood_conjugated_into hQG hKo K.one_mem
  obtain ⟨H₂, hH₂, hH₂V₂⟩ := hB.2.mem_iff.mp (hV₂o.mem_nhds hV₂one)
  obtain ⟨V₁, hV₁o, hV₁one, hV₁⟩ := exists_open_neighborhood_conjugated_into hQG
    (hB.1 H₂ hH₂).2.2.1 H₂.one_mem
  have hpre : IsOpen {p : standardParabolicPoints i ν J | (h.projection p : rationalPoints G) ∈ K} :=
    hKo.preimage (continuous_subtype_val.comp hmP)
  obtain ⟨VP, hVPo, hVP⟩ := isOpen_induced_iff.mp hpre
  have hVPone : 1 ∈ VP := by
    have hp : (1 : standardParabolicPoints i ν J) ∈
        {p : standardParabolicPoints i ν J | (h.projection p : rationalPoints G) ∈ K} := by
      change (h.projection 1 : rationalPoints G) ∈ K
      rw [map_one, Subgroup.coe_one]
      exact K.one_mem
    rw [← hVP] at hp
    exact hp
  obtain ⟨H₁, hH₁, hH₁V⟩ := hB.2.mem_iff.mp ((hV₁o.inter hVPo).mem_nhds ⟨hV₁one, hVPone⟩)
  let Opp := standardOppositeUnipotentPoints i ν ∅
  let V : Set (rationalPoints G) := (H₁ ⊓ Opp : Subgroup (rationalPoints G))
  have hfac (k : rationalPoints G) (hk : k ∈ H₁) :
      ∃ p : standardParabolicPoints i ν J, (p : rationalPoints G) ∈ H₁ ∧
        ∃ v ∈ V, k = (p : rationalPoints G) * v := by
    obtain ⟨⟨l, m, n⟩, heq⟩ := (hmembers H₁ hH₁).1.2 ⟨k⁻¹, H₁.inv_mem hk⟩
    have he : k⁻¹ = (l : rationalPoints G) * m * n := (congrArg Subtype.val heq).symm
    have hn : (n : rationalPoints G) ∈ standardParabolicPoints i ν ∅ :=
      standardUnipotent_le_standardParabolic i ν ∅ _ n.2.2
    have hm : (m : rationalPoints G) ∈ standardParabolicPoints i ν ∅ :=
      standardLevi_le_standardParabolic i ν ∅ _ m.2.2
    have hp : (n : rationalPoints G)⁻¹ * (m : rationalPoints G)⁻¹ ∈ standardParabolicPoints i ν J := by
      apply standardParabolicPoints_empty_le hG hi hν hJ
      exact (standardParabolicPoints i ν ∅).mul_mem ((standardParabolicPoints i ν ∅).inv_mem hn)
        ((standardParabolicPoints i ν ∅).inv_mem hm)
    refine ⟨⟨_, hp⟩, H₁.mul_mem (H₁.inv_mem n.2.1) (H₁.inv_mem m.2.1),
      (l : rationalPoints G)⁻¹, ⟨H₁.inv_mem l.2.1, Opp.inv_mem l.2.2⟩, ?_⟩
    calc k = (k⁻¹)⁻¹ := (inv_inv k).symm
      _ = _ := by rw [he]; change _ = _ * _ * _; group
  have hsmall (p : standardParabolicPoints i ν J) (hp : (p : rationalPoints G) ∈ H₁) :
      (h.projection p : rationalPoints G) ∈ K := by
    have hPV : p ∈ ((↑) : standardParabolicPoints i ν J → rationalPoints G) ⁻¹' VP := (hH₁V hp).2
    rw [hVP] at hPV
    exact hPV
  let D := incM '' rationalMinimalClosedChamber hG hi hν
  have hcontract (m : standardLeviPoints i ν J) (hm : m ∈ D) (v : rationalPoints G) (hv : v ∈ V) :
      (m : rationalPoints G)⁻¹ * v * (m : rationalPoints G) ∈ K := by
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    obtain ⟨k₁, hk₁, k₂, hk₂, y, hy, hm₀eq⟩ := hreduce m₀ hm₀
    let a := (minimalLeviUniformizer (i := i) (ν := ν) y : rationalPoints G)
    have ha : a ∈ standardComponentCAplus i ν ∅ q₀ := by
      rw [show a = Aubert.General.uniformizerPowers i (.ofAdd y) from coe_minimalLeviUniformizer y]
      exact (uniformizerPowers_mem_standardComponentChambers hi
        ⟨ν, isStandardCocharacter_empty_self i ν⟩ hA₀ y (by simp) hy).2
    let v₁ := (k₁ : rationalPoints G)⁻¹ * v * (k₁ : rationalPoints G)
    have hv₁H : v₁ ∈ H₂ := hV₁ _ ⟨k₁, hk₁, rfl⟩ _ (hH₁V hv.1).1
    have hn := standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints hG hi hν
      (isStandardCocharacter_empty_self i ν)
    have hv₁O : v₁ ∈ Opp := by
      have hk := hn ((standardLeviPoints i ν ∅).inv_mem k₁.property)
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hk v).mp hv.2
    have hcontra := ((hmembers H₂ hH₂).2.2.1 a ha).2 ⟨v₁, ⟨hv₁H, hv₁O⟩, rfl⟩
    have haH : a⁻¹ * v₁ * a ∈ H₂ := by
      change a⁻¹ * v₁ * a ∈ (H₂.toSubmonoid : Set (rationalPoints G))
      simpa only [inv_inv] using hcontra.1
    have he : (incM m₀ : rationalPoints G) = (k₁ : rationalPoints G) * a * (k₂ : rationalPoints G) :=
      congrArg Subtype.val hm₀eq
    rw [he]
    have heq : ((k₁ : rationalPoints G) * a * (k₂ : rationalPoints G))⁻¹ * v *
        ((k₁ : rationalPoints G) * a * (k₂ : rationalPoints G)) =
        (k₂ : rationalPoints G)⁻¹ * (a⁻¹ * v₁ * a) * (k₂ : rationalPoints G) := by
      dsimp only [v₁]
      group
    rw [heq]
    exact hV₂ _ ⟨k₂, hk₂, rfl⟩ _ (hH₂V₂ haH)
  obtain ⟨C, hC, hCbound⟩ := (rationalLeviData hG hi hν hJ hKo hKc).exists_sqrt_mul_xi_le_xi_of_factorization
    hKo hPK hMK (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)
    (hB.1 H₁ hH₁).2.2.1 hfac hsmall hcontract
  refine ⟨C, hC, fun m hm => ?_⟩
  have hh := hCbound (incM m) ⟨m, hm, rfl⟩
  rw [standardHalfModulus, Complex.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact hh

end Langlands.HarishChandraSchwartz
