import Langlands.Representation.Jacquet.StandardCasselmanDimensionThreshold
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviDominantReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalComponentValuation
import Langlands.HarmonicAnalysis.Distribution.RenardCenterCriteriaProof

/-! # Proposition I.4.3 on the full minimal Levi with a representation-independent threshold

For a connected reductive group with Renard's simultaneous basis data and the minimal-Levi
Cartan covering of a compact `K0`, a face `J ⊆ Δ` and a basis member `K₁`, there is a smaller
basis member `K₂` such that for every `d : ℕ` there is one `t > 0` with the following property:
for every admissible representation `ρ` whose `K₂`-fixed vectors have dimension at most `d`, every
stable pairing `b` of the I.4.1 data of `P_J` for `ρ` and all `K₁`-fixed `v`, `ℓ`, the identity
`ℓ(ρ(m) v) = b(ǰ(ℓ), j(ρ(m) v))` holds at every point `m` of the actual minimal Levi `M_0(F)`
in the closed chamber with `⟨α, H_0(m)⟩ ≥ t` for every simple root `α ∉ J`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Reduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

set_option maxHeartbeats 600000 in
/-- **Compact dominant reduction with depth control.** For the minimal-Levi Cartan covering of
a compact `K0` there is a compact subset `Q` of `M_0(F)` such that every `m ∈ M̄_0^+` is
`k₁ ϖ^y k₂` with `k₁, k₂ ∈ Q`, `y` dominant and `⟨α, H_0(m)⟩ ≤ ⟨α, y⟩` for every simple root
`α`. (The argument of `hasCompactDominantMinimalLeviReduction_of_cartanCovering`, keeping the
inequality it proves along the way.) -/
theorem exists_compact_dominant_depth_reduction [LocallyOfFiniteType G.X.hom]
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0) :
    ∃ Q : Set (standardLeviPoints i ν ∅), IsCompact Q ∧
      ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
        ∃ k₁ ∈ Q, ∃ k₂ ∈ Q, ∃ y : cocharacterLattice S,
          (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) ∧
          (∀ α ∈ simpleRelativeRoots i ν,
            RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν m) ≤ latticePairing S α y) ∧
          m = k₁ * minimalLeviUniformizer (i := i) (ν := ν) y * k₂ := by
  classical
  obtain ⟨F0, hcover⟩ := hcover
  let f0 : centralizerPoints i → standardLeviPoints i ν ∅ := fun f =>
    ⟨f, by rw [standardLeviPoints_empty_eq_centralizerPoints hG hi hν]; exact f.2⟩
  let R := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν |>.toFinset
  obtain ⟨b, hb⟩ := ((R.product F0).image fun p : characterLattice S × centralizerPoints i =>
    RealTorusSpace.eval S p.1 (rationalMinimalH0 hG hi hν (f0 p.2))).exists_le
  obtain ⟨N, hN⟩ := exists_nat_ge b
  let c : cocharacterLattice S := N • ν
  have hshift : ∀ α ∈ simpleRelativeRoots i ν, ∀ f ∈ F0,
      RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν (f0 f)) ≤
        (latticePairing S α c : ℝ) := by
    intro α hα f hf
    have hαR : α ∈ R := by simpa [R] using hα
    have hpair : (α, f) ∈ R.product F0 := Finset.mem_product.mpr ⟨hαR, hf⟩
    have hbound := hb _ (Finset.mem_image_of_mem _ hpair)
    have hαν : (1 : ℝ) ≤ latticePairing S α ν := by
      have hpos := (simpleRelativeRoots_subset_positive i ν hα).2
      exact_mod_cast (show (1 : ℤ) ≤ latticePairing S α ν by omega)
    have hmul := mul_le_mul_of_nonneg_left hαν (Nat.cast_nonneg (α := ℝ) N)
    calc RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν (f0 f))
        ≤ b := hbound
      _ ≤ N := hN
      _ ≤ (latticePairing S α c : ℝ) := by
        simpa only [c, map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_one] using hmul
  let Q0 : Set (standardLeviPoints i ν ∅) := {m | (m : rationalPoints G) ∈ K0}
  have hQ0 : IsCompact Q0 :=
    (isClosed_standardLeviPoints i ν ∅).isClosedEmbedding_subtypeVal.isCompact_preimage hK0
  let Q1 : Set (standardLeviPoints i ν ∅) :=
    ⋃ f ∈ F0, (fun k : standardLeviPoints i ν ∅ =>
      k * f0 f * minimalLeviUniformizer (i := i) (ν := ν) (-c)) '' Q0
  have hQ1 : IsCompact Q1 :=
    F0.isCompact_biUnion fun f _ =>
      hQ0.image ((continuous_id.mul continuous_const).mul continuous_const)
  refine ⟨Q0 ∪ Q1, hQ0.union hQ1, fun m hm => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hmeq⟩ := hcover m m.2
  obtain ⟨y, rfl⟩ := ha.1
  change (m : rationalPoints G) =
    k₁ * (f : rationalPoints G) * Langlands.Aubert.General.uniformizerPowers i y * k₂ at hmeq
  let m₁ : standardLeviPoints i ν ∅ := ⟨k₁, hk₁.2⟩
  let m₂ : standardLeviPoints i ν ∅ := ⟨k₂, hk₂.2⟩
  have h₁ : rationalMinimalH0 hG hi hν m₁ = 0 :=
    rationalMinimalH0_eq_zero_of_mem_compact hG hi hν hK0 hk₁.1
  have h₂ : rationalMinimalH0 hG hi hν m₂ = 0 :=
    rationalMinimalH0_eq_zero_of_mem_compact hG hi hν hK0 hk₂.1
  have hm' : m = m₁ * f0 f * minimalLeviUniformizer (i := i) (ν := ν) y.toAdd * m₂ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_minimalLeviUniformizer]
    exact hmeq
  have hH : rationalMinimalH0 hG hi hν m =
      rationalMinimalH0 hG hi hν (f0 f) + (1 : ℝ) ⊗ₜ[ℤ] y.toAdd := by
    rw [hm']
    simp only [rationalMinimalH0_mul, h₁, h₂, rationalMinimalH0_minimalLeviUniformizer,
      zero_add, add_zero]
  refine ⟨m₁ * f0 f * minimalLeviUniformizer (i := i) (ν := ν) (-c),
    Or.inr (Set.mem_iUnion₂.mpr ⟨f, hf, ⟨m₁, hk₁.1, rfl⟩⟩),
    m₂, Or.inl hk₂.1, y.toAdd + c, ?_, ?_, ?_⟩
  · intro α hα
    have hdom := hm α hα
    rw [hH, map_add, RealTorusSpace.eval_tmul, one_mul] at hdom
    have h := hshift α hα f hf
    have hc : (0 : ℝ) ≤ (latticePairing S α (y.toAdd + c) : ℝ) := by
      simp only [map_add, Int.cast_add]
      linarith
    exact_mod_cast hc
  · intro α hα
    rw [hH, map_add, RealTorusSpace.eval_tmul, one_mul]
    have h := hshift α hα f hf
    simp only [map_add, Int.cast_add]
    linarith
  · have hw : minimalLeviUniformizer (i := i) (ν := ν) y.toAdd =
        minimalLeviUniformizer (i := i) (ν := ν) (-c) *
          minimalLeviUniformizer (i := i) (ν := ν) (y.toAdd + c) := by
      rw [← minimalLeviUniformizer_add]
      congr 1
      abel
    rw [hm', hw]
    group

end Reduction

section Region

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (A : Set (characterLattice S) → CommGroupScheme (Spec (CommRingCat.of F)))
  (q : ∀ J, (A J).toGrp ⟶ S.toGrp)
  (hA : ∀ J, J ⊆ simpleRelativeRoots i ν →
    IsCompatibleStandardSplitComponent i ν J (A J) (q J))
  (hmem : ∀ J, J ⊆ simpleRelativeRoots i ν → ∀ K ∈ B,
    StandardParabolicBasisMember i ν J (q J) K)
  (ζ : Set (characterLattice S) → cocharacterLattice S)
  (hζ : ∀ J, J ⊆ simpleRelativeRoots i ν → IsStandardCocharacter i ν J (ζ J))

include hB hA hmem hζ in
open Langlands.Jacquet in
/-- **Proposition I.4.3 on `M̄_0^+` with a representation-independent threshold.** For a face
`J ⊆ Δ` and a basis member `K₁` there is a basis member `K₂ ≤ K₁` such that for every `d` there
is `t > 0` with `ℓ(ρ(m) v) = b(ǰ(ℓ), j(ρ(m) v))` for every admissible `ρ` with
`dim V^{K₂} ≤ d`, every stable pairing `b` of the I.4.1 data of `P_J` for `ρ`, all `K₁`-fixed
`v`, `ℓ` and every `m` in the closed chamber of the actual minimal Levi with `⟨α, H_0(m)⟩ ≥ t`
for all simple `α ∉ J` (`rationalConstantTermThresholdRegion`). -/
theorem exists_region_dimension_threshold
    (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {K₁ : Subgroup (rationalPoints G)} (hK₁ : K₁ ∈ B) :
    ∃ K₂ ∈ B, K₂ ≤ K₁ ∧ ∀ d : ℕ, ∃ t : ℝ, 0 < t ∧
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
        (b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ),
        (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
          (hmem J hJ)).IsStablePairing ρ hρ.1 b →
        Module.finrank ℂ (fixedVectors ρ K₂) ≤ d →
        ∀ v ∈ fixedVectors ρ K₁, ∀ ℓ ∈ fixedVectors (smoothContragredient ρ) K₁,
        ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν J t,
          smoothDualPairing ρ ℓ (ρ (m : rationalPoints G) v) =
            b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ (m : rationalPoints G) v)) := by
  classical
  obtain ⟨Q, hQ, hred⟩ := exists_compact_dominant_depth_reduction hG hi hν hK0 hcover
  let C : Set (rationalPoints G) :=
    Subtype.val '' Q ∪ (fun x => x⁻¹) '' (Subtype.val '' Q)
  have hC : IsCompact C :=
    (hQ.image continuous_subtype_val).union
      ((hQ.image continuous_subtype_val).image continuous_inv)
  let K₁' := basisOpenSubgroup hB hK₁
  obtain ⟨U, hU⟩ := HarmonicAnalysis.Distribution.RenardCenter.exists_openSubgroup_conj_mem C hC K₁'
  obtain ⟨K₂, hK₂B, hK₂U⟩ := hB.2.mem_iff.mp ((U ⊓ K₁').mem_nhds_one)
  have hK₂le : K₂ ≤ K₁ := fun x hx => (OpenSubgroup.mem_inf.mp (hK₂U hx)).2
  have hK₂U' : ∀ x ∈ K₂, x ∈ U := fun x hx => (OpenSubgroup.mem_inf.mp (hK₂U hx)).1
  refine ⟨K₂, hK₂B, hK₂le, fun d => ?_⟩
  obtain ⟨T, hT⟩ := exists_dimension_threshold_standardCasselmanPairing.{u, uV} hG hi hν hB
    A q hA hmem ζ hζ hJ hK₂B d
  refine ⟨|T| + 1, by positivity, ?_⟩
  intro V _ _ ρ hρ b hb hd v hv ℓ hℓ m hm
  obtain ⟨hmC, hdeep⟩ := hm
  obtain ⟨k₁, hk₁, k₂, hk₂, y, hy, hyH, rfl⟩ := hred m hmC
  set a := Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) with ha_def
  have hw : ρ (k₂ : rationalPoints G) v ∈ fixedVectors ρ K₂ := by
    intro k
    have hk : (k₂ : rationalPoints G)⁻¹ * (k : rationalPoints G) * (k₂ : rationalPoints G) ∈
        K₁ := by
      have h := hU ((k₂ : rationalPoints G)⁻¹) (Or.inr ⟨(k₂ : rationalPoints G), ⟨k₂, hk₂, rfl⟩,
        rfl⟩) k (hK₂U' k k.property)
      have h' : (k₂ : rationalPoints G)⁻¹ * (k : rationalPoints G) * (k₂ : rationalPoints G) ∈
          K₁' := by simpa only [inv_inv] using h
      exact h'
    change ρ (k : rationalPoints G) (ρ (k₂ : rationalPoints G) v) = ρ (k₂ : rationalPoints G) v
    calc ρ (k : rationalPoints G) (ρ (k₂ : rationalPoints G) v) =
        ρ (k₂ : rationalPoints G) (ρ ((k₂ : rationalPoints G)⁻¹ * (k : rationalPoints G) *
          (k₂ : rationalPoints G)) v) := by
          simp only [← Module.End.mul_apply, ← map_mul]
          congr 2
          group
      _ = ρ (k₂ : rationalPoints G) v := by rw [apply_eq_of_mem_fixedVectors ρ hv hk]
  have hℓ' : smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ ∈
      fixedVectors (smoothContragredient ρ) K₂ := by
    intro k
    have hk : (k₁ : rationalPoints G) * (k : rationalPoints G) * (k₁ : rationalPoints G)⁻¹ ∈
        K₁ :=
      hU (k₁ : rationalPoints G) (Or.inl ⟨k₁, hk₁, rfl⟩) k (hK₂U' k k.property)
    change smoothContragredient ρ (k : rationalPoints G)
        (smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ) =
      smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ
    calc smoothContragredient ρ (k : rationalPoints G)
          (smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ) =
        smoothContragredient ρ (k₁ : rationalPoints G)⁻¹
          (smoothContragredient ρ ((k₁ : rationalPoints G) * (k : rationalPoints G) *
            (k₁ : rationalPoints G)⁻¹) ℓ) := by
          simp only [← Module.End.mul_apply, ← map_mul]
          congr 2
          group
      _ = smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ := by
          rw [apply_eq_of_mem_fixedVectors (smoothContragredient ρ) hℓ hk]
  have hdeep' : ∀ α ∈ simpleRelativeRoots i ν, α ∉ J → T < latticePairing S α y := by
    intro α hα hαJ
    have h1 := hdeep α ⟨hα, hαJ⟩
    have h2 := hyH α hα
    have h3 : T < |T| + 1 := by linarith [le_abs_self T]
    linarith
  have key := hT ρ hρ b hb hd _ hw _ hℓ' y hy hdeep'
  have hAd := standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
    ρ hρ
  have hk₁J : (k₁ : rationalPoints G) ∈ standardLeviPoints i ν J :=
    standardLeviPoints_empty_le hG hi hν J k₁.2
  have hinv := hb.map_action hAd ⟨(k₁ : rationalPoints G), hk₁J⟩
    (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
      (smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ))
    (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ a (ρ (k₂ : rationalPoints G) v)))
  have hpt : ((k₁ * minimalLeviUniformizer (i := i) (ν := ν) y * k₂ : standardLeviPoints i ν ∅) :
      rationalPoints G) = (k₁ : rationalPoints G) * a * (k₂ : rationalPoints G) := by
    simp only [Subgroup.coe_mul, coe_minimalLeviUniformizer, ha_def]
  have hρpt : ρ ((k₁ * minimalLeviUniformizer (i := i) (ν := ν) y * k₂ :
      standardLeviPoints i ν ∅) : rationalPoints G) v =
      ρ (k₁ : rationalPoints G) (ρ a (ρ (k₂ : rationalPoints G) v)) := by
    rw [hpt, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hℓeq : smoothContragredient ρ (k₁ : rationalPoints G)
      (smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ) = ℓ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hρpt]
  calc smoothDualPairing ρ ℓ (ρ (k₁ : rationalPoints G) (ρ a (ρ (k₂ : rationalPoints G) v)))
      = smoothDualPairing ρ (smoothContragredient ρ (k₁ : rationalPoints G)⁻¹ ℓ)
          (ρ a (ρ (k₂ : rationalPoints G) v)) := by
        rw [smoothDualPairing_action, inv_inv]
    _ = _ := key
    _ = _ := hinv.symm
    _ = _ := by
        congr 2
        exact congrArg (Jacquet.mk (smoothContragredient ρ)
          (standardOppositeUnipotentPoints i ν J)) hℓeq

end Region

end Langlands.HarishChandraSchwartz
