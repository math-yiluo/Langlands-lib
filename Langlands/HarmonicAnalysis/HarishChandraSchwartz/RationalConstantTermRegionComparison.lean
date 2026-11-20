import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviDimensionThreshold

/-! # The constant term along `P_J` on the threshold region, uniformly in the representation

Combining the representation-independent threshold of `exists_region_dimension_threshold` with
the uniqueness of right-finite constant terms, this module proves: for a face `J`, an arbitrary
compatible split component `A` of `M_J` (with a standard cocharacter of `J`) and a basis member
`K₁`, there is a basis member `K₂ ≤ K₁` such that for every `d` there is `t > 0` with
`f(m) = δ_{U_J}(m)^{1/2} f_{P_J}(m)` for every admissible `ρ` with `dim V^{K₂} ≤ d`, every
`f` in the span of the coefficients of `K₁`-fixed vectors and functionals, and every point `m` of
the actual minimal Levi in the threshold region; here `f_{P_J}` is the published
`standardConstantTerm` for `A`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Cone

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {q : A.toGrp ⟶ S.toGrp}

omit [IsAffineHom G.X.hom] in
/-- The order of a restricted character at a point of `A(F)` is the order of the character at
the image point of `S(F)`. -/
theorem characterOrder_componentCharacterRestriction (α : characterLattice S)
    (x : rationalPoints A.toGrp) :
    BruhatTits.Cartan.RenardLeviCones.characterOrder A (componentCharacterRestriction q α) x =
      BruhatTits.Cartan.RenardLeviCones.characterOrder S α (rationalPoints.map q x) := by
  unfold BruhatTits.Cartan.RenardLeviCones.characterOrder componentCharacterRestriction
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    AddEquiv.symm_apply_apply]
  exact Plancherel.rationalCharacterValuation_characterRestrict q _ x

/-- **The source's cone lies in the threshold region.** For a compatible split component `A` of
`M_J` and `t ≥ 0`, the image in `M_0(F)` of every point `x ∈ A(F)` with `|α(x)|_F < q^{-t}` for
all `α ∈ Δ(P_J)` lies in `rationalConstantTermThresholdRegion J t`. -/
theorem mem_thresholdRegion_of_mem_standardCone [LocallyOfFiniteType G.X.hom]
    {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hA : IsCompatibleStandardSplitComponent i ν J A q)
    {t : ℝ} (ht : 0 ≤ t) {x : rationalPoints A.toGrp}
    (hx : x ∈ standardCone i ν J q ((LocalField.residueCardinality F : ℝ) ^ (-t))) :
    (⟨rationalPoints.map (q ≫ i) x, map_mem_standardLeviPoints_empty q x⟩ :
        standardLeviPoints i ν ∅) ∈ rationalConstantTermThresholdRegion hG hi hν J t := by
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hH : ∀ α, RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν
      ⟨rationalPoints.map (q ≫ i) x, map_mem_standardLeviPoints_empty q x⟩) =
      (BruhatTits.Cartan.RenardLeviCones.characterOrder A (componentCharacterRestriction q α) x :
        ℝ) := by
    intro α
    rw [characterOrder_componentCharacterRestriction]
    exact eval_rationalComponentH0 hG hi hν α x
  have hout : ∀ α ∈ simpleRelativeRoots i ν \ J,
      t < (BruhatTits.Cartan.RenardLeviCones.characterOrder A
        (componentCharacterRestriction q α) x : ℝ) := by
    intro α hα
    have h := hx _ ⟨α, hα, rfl⟩
    rw [BruhatTits.Cartan.RenardLeviCones.characterNorm_eq_rpow] at h
    have h' := (Real.rpow_lt_rpow_left_iff hq).mp h
    linarith
  have hin : ∀ α ∈ J, BruhatTits.Cartan.RenardLeviCones.characterOrder A
      (componentCharacterRestriction q α) x = 0 := by
    intro α hα
    have hsplit : IsSplitTorus A.toGrp := hA.1.1
    have := CocharacterUniformizer.latticePairing_isPerfPair F A hsplit
    have hzero : componentCharacterRestriction q α = 0 := by
      apply (LinearMap.IsPerfPair.bijective_left (latticePairing A)).injective
      apply LinearMap.ext
      intro c
      rw [map_zero, LinearMap.zero_apply,
        Aubert.General.latticePairing_componentCharacterRestriction]
      exact hA.latticePairing_eq_zero hJ c hα
    rw [hzero]
    unfold BruhatTits.Cartan.RenardLeviCones.characterOrder
    rw [map_zero, map_zero]
  refine ⟨fun α hα => ?_, fun α hα => ?_⟩
  · rw [hH]
    by_cases hαJ : α ∈ J
    · rw [hin α hαJ]
      simp
    · exact ht.trans (hout α ⟨hα, hαJ⟩).le
  · rw [hH]
    exact (hout α hα).le

end Cone

section Comparison

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
  (hK0 : IsCompact (K0 : Set (rationalPoints G)))
  (hcover : StandardLeviCartanCovering F i ν ∅ K0)

include hB hA hmem hζ hK0 hcover in
open Langlands.Jacquet in
/-- **Comparison of constant terms.** The constant term `m ↦ b(ǰ(ℓ), J_δ(m) j(v))` of the
coefficient `x ↦ ℓ(ρ(x) v)` built from a stable pairing `b` of the I.4.1 data of `P_J` is a
constant term in the sense of Proposition I.6.2 for **every** compatible split component `A'` of
`M_J`: the asymptotic identity on the cone of `A'` follows from the region theorem, since the
cone lies in the threshold region. -/
theorem isStandardConstantTerm_coefficientConstantTerm_of_region
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A' : CommGroupScheme (Spec (CommRingCat.of F))} {q' : A'.toGrp ⟶ S.toGrp}
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
      Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
    (hb : (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
      (hmem J hJ)).IsStablePairing ρ hρ.1 b)
    (ℓ : SmoothDual ρ) (v : V) :
    IsStandardConstantTerm hA' (fun x => smoothDualPairing ρ ℓ (ρ x v))
      ((standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
        (hmem J hJ)).coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ v) := by
  intro m'
  obtain ⟨ℓ', hℓ'_def⟩ : ∃ ℓ' : SmoothDual ρ,
      ℓ' = smoothContragredient ρ (m' : rationalPoints G)⁻¹ ℓ := ⟨_, rfl⟩
  obtain ⟨U₁, hU₁⟩ := hρ.1 v
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ'
  obtain ⟨K₁, hK₁B, hK₁U⟩ := hB.2.mem_iff.mp (U₁ ⊓ U₂).mem_nhds_one
  have hv : v ∈ fixedVectors ρ K₁ :=
    mem_fixedVectors_of_le ρ (K := basisOpenSubgroup hB hK₁B) (fun x hx => (hK₁U hx).1) hU₁
  have hℓ' : ℓ' ∈ fixedVectors (smoothContragredient ρ) K₁ :=
    mem_fixedVectors_of_le (smoothContragredient ρ) (K := basisOpenSubgroup hB hK₁B)
      (fun x hx => (hK₁U hx).2) hU₂
  obtain ⟨K₂, -, -, hK₂⟩ := exists_region_dimension_threshold.{u, uV} hG hi hν hB A q hA hmem
    ζ hζ hK0 hcover hJ hK₁B
  obtain ⟨t, ht, hreg⟩ := hK₂ (Module.finrank ℂ (fixedVectors ρ K₂))
  have hq0 : (0 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast (Nat.zero_lt_one.trans (LocalField.residueCardinality_gt_one F))
  refine ⟨(LocalField.residueCardinality F : ℝ) ^ (-t), Real.rpow_pos_of_pos hq0 _,
    fun x hx => ?_⟩
  have hm₀ := mem_thresholdRegion_of_mem_standardCone hG hi hν hJ hA' ht.le hx
  have key := hreg ρ hρ b hb le_rfl v hv ℓ' hℓ' _ hm₀
  have hAd := standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
    ρ hρ
  have hinv := hb.map_action hAd m'⁻¹
    (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
    (Jacquet.mk ρ (standardUnipotentPoints i ν J)
      (ρ (m' : rationalPoints G) (ρ (rationalPoints.map (q' ≫ i) x) v)))
  have hpt : ρ ((m' * standardComponentHom hA' x : standardLeviPoints i ν J) :
      rationalPoints G) v =
      ρ (m' : rationalPoints G) (ρ (rationalPoints.map (q' ≫ i) x) v) := by
    rw [Subgroup.coe_mul, coe_standardComponentHom, map_mul, Module.End.mul_apply]
  have h2 : smoothDualPairing ρ ℓ
      (ρ (m' : rationalPoints G) (ρ (rationalPoints.map (q' ≫ i) x) v)) =
      smoothDualPairing ρ ℓ' (ρ (rationalPoints.map (q' ≫ i) x) v) := by
    rw [hℓ'_def, smoothDualPairing_action, inv_inv]
  have e1 : Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ' =
      action (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)
        (standardLeviPoints i ν J)
        (standardLeviPoints_le_normalizer_standardOppositeUnipotentPoints hG hi hν (hζ J hJ))
        m'⁻¹ (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ) := by
    rw [action_mk, hℓ'_def]
    rfl
  have e2 : Jacquet.mk ρ (standardUnipotentPoints i ν J)
      (ρ (rationalPoints.map (q' ≫ i) x) v) =
      action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) m'⁻¹
        (Jacquet.mk ρ (standardUnipotentPoints i ν J)
          (ρ (m' : rationalPoints G) (ρ (rationalPoints.map (q' ≫ i) x) v))) := by
    rw [action_mk]
    exact congrArg _ (ρ.inv_self_apply (m' : rationalPoints G) _).symm
  have h : smoothDualPairing ρ ℓ
      (ρ ((m' * standardComponentHom hA' x : standardLeviPoints i ν J) : rationalPoints G) v) =
      b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
        (Jacquet.mk ρ (standardUnipotentPoints i ν J)
          (ρ ((m' * standardComponentHom hA' x : standardLeviPoints i ν J) :
            rationalPoints G) v)) := by
    rw [hpt, h2]
    refine key.trans ?_
    rw [e1, e2]
    exact hinv
  exact StablePairingData.inv_sqrt_mul_eq_coefficientConstantTerm
    (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)) ρ b
    (standardRadicalModulus i ν J) ℓ v (m' * standardComponentHom hA' x) h

include hB hA hmem hζ in
open Langlands.Jacquet in
/-- The constant term of a coefficient built from a stable pairing is right finite for every
compatible split component of `M_J`. -/
theorem isRightFinite_coefficientConstantTerm_standard
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A' : CommGroupScheme (Spec (CommRingCat.of F))} {q' : A'.toGrp ⟶ S.toGrp}
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
      Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
    (hb : (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
      (hmem J hJ)).IsStablePairing ρ hρ.1 b)
    (ℓ : SmoothDual ρ) (v : V) :
    IsRightFinite (standardComponentHom hA').range
      ((standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
        (hmem J hJ)).coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ v) := by
  have hAd := standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
    ρ hρ
  have hδ := isOpen_ker_standardRadicalModulus (i := i) (ν := ν) (J := J)
  have hbasis := hasIwahoriContractionBasis_standard hi (hζ J hJ) hB (hA J hJ) (hmem J hJ)
  obtain ⟨B', hB', hmemB⟩ := hb.exists_admissible_coefficientConstantTerm hAd
    (standardRadicalModulus i ν J) hδ hρ hbasis ℓ v
  exact isRightFinite_of_mem_coefficientFunctionSpace hB' _
    (standardComponentHom_range_central hA') hmemB

open Langlands.Jacquet in
/-- At a point `m ∈ M_J(F)`, the pairing of the class of `ρ(m) v` with `ǰ(ℓ)` is
`δ_{U_J}(m)^{1/2}` times the constant term of the coefficient at `m`. -/
theorem pairing_eq_sqrt_mul_coefficientConstantTerm
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V)
    (b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
      Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ)
    (ℓ : SmoothDual ρ) (v : V) (m : standardLeviPoints i ν J) :
    b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
        (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ (m : rationalPoints G) v)) =
      ((NNReal.sqrt (standardRadicalModulus i ν J m : ℝ≥0) : ℝ) : ℂ) *
        (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
          (hmem J hJ)).coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ v m :=
  StablePairingData.apply_mk_eq_sqrt_mul_normalized
    (D := standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ))
    (standardRadicalModulus i ν J)
    (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ) m v

open Langlands.Jacquet in
/-- On `M_0(F)`, the pairing of a coefficient is `δ_{U_J}^{1/2}` times its constant term. -/
theorem pairing_eq_standardHalfModulus_mul_coefficientConstantTerm
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V)
    (b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
      Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ)
    (ℓ : SmoothDual ρ) (v : V) (m : standardLeviPoints i ν ∅) :
    b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
        (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ (m : rationalPoints G) v)) =
      standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
        (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
          (hmem J hJ)).coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ v
          (minimalLeviInclusion hG hi hν J m) := by
  have h := pairing_eq_sqrt_mul_coefficientConstantTerm hG hi hν hB A q hA hmem ζ hζ hJ ρ b ℓ v
    (minimalLeviInclusion hG hi hν J m)
  rw [coe_minimalLeviInclusion] at h
  rw [standardHalfModulus]
  exact h

include hB hA hmem hζ hK0 hcover in
open Langlands.Jacquet in
/-- **One coefficient.** If the asymptotic identity of the stable pairing holds for the
coefficient `x ↦ ℓ(ρ(x) v)` on the threshold region, its constant term
`m ↦ b(ǰ(ℓ), J_δ(m) j(v))` is right finite, is a constant term for `A'`, and satisfies
`ℓ(ρ(m) v) = δ_{U_J}(m)^{1/2} f_P(m)` on the region. -/
theorem exists_constantTerm_data_of_region
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A' : CommGroupScheme (Spec (CommRingCat.of F))} {q' : A'.toGrp ⟶ S.toGrp}
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
    {b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
      Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
    (hb : (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
      (hmem J hJ)).IsStablePairing ρ hρ.1 b)
    (ℓ : SmoothDual ρ) (v : V) {t : ℝ}
    (hreg : ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν J t,
      smoothDualPairing ρ ℓ (ρ (m : rationalPoints G) v) =
        b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
          (Jacquet.mk ρ (standardUnipotentPoints i ν J) (ρ (m : rationalPoints G) v))) :
    ∃ φ : standardLeviPoints i ν J → ℂ,
      IsRightFinite (standardComponentHom hA').range φ ∧
      IsStandardConstantTerm hA' (fun x => smoothDualPairing ρ ℓ (ρ x v)) φ ∧
      ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν J t,
        smoothDualPairing ρ ℓ (ρ (m : rationalPoints G) v) =
          standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
            φ (minimalLeviInclusion hG hi hν J m) := by
  refine ⟨(standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
    (hmem J hJ)).coefficientConstantTerm ρ b (standardRadicalModulus i ν J) ℓ v,
    isRightFinite_coefficientConstantTerm_standard hG hi hν hB A q hA hmem ζ hζ hJ hA' ρ hρ hb ℓ v,
    isStandardConstantTerm_coefficientConstantTerm_of_region hG hi hν hB A q hA hmem
      ζ hζ hK0 hcover hJ hA' ρ hρ hb ℓ v, fun m hm => ?_⟩
  rw [hreg m hm]
  exact pairing_eq_standardHalfModulus_mul_coefficientConstantTerm hG hi hν hB A q hA hmem ζ hζ
    hJ ρ b ℓ v m

include hB hA hmem hζ hK0 hcover in
open Langlands.Jacquet in
/-- **The constant-term threshold on the minimal Levi, uniformly in the representation.** For
a face `J`, a compatible split component `A'` of `M_J` with a standard cocharacter of `J`, and a
basis member `K₁`, there is a basis member `K₂ ≤ K₁` such that for every `d` there is `t > 0`
with `f(m) = δ_{U_J}(m)^{1/2} f_{P_J}(m)` (`standardConstantTerm hA'`) for every admissible `ρ`
with `dim V^{K₂} ≤ d`, every `f` in the span of the coefficients `x ↦ ℓ(ρ(x) v)` with `K₁`-fixed
`v` and `ℓ`, and every `m ∈ M̄_0^+` with `⟨α, H_0(m)⟩ ≥ t` for all simple `α ∉ J`. -/
theorem exists_constantTerm_dimension_threshold
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A' : CommGroupScheme (Spec (CommRingCat.of F))} {q' : A'.toGrp ⟶ S.toGrp}
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    {ζ' : cocharacterLattice S} (hζ' : IsStandardCocharacter i ν J ζ')
    {K₁ : Subgroup (rationalPoints G)} (hK₁ : K₁ ∈ B) :
    ∃ K₂ ∈ B, K₂ ≤ K₁ ∧ ∀ d : ℕ, ∃ t : ℝ, 0 < t ∧
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V), IsAdmissible ρ →
        Module.finrank ℂ (fixedVectors ρ K₂) ≤ d →
        ∀ f ∈ Submodule.span ℂ {g : rationalPoints G → ℂ | ∃ v ∈ fixedVectors ρ K₁,
          ∃ ℓ ∈ fixedVectors (smoothContragredient ρ) K₁,
            g = fun x => smoothDualPairing ρ ℓ (ρ x v)},
        ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν J t,
          f (m : rationalPoints G) =
            standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
              standardConstantTerm hA' f (minimalLeviInclusion hG hi hν J m) := by
  obtain ⟨K₂, hK₂B, hK₂le, hK₂⟩ := exists_region_dimension_threshold.{u, uV} hG hi hν hB A q
    hA hmem ζ hζ hK0 hcover hJ hK₁
  refine ⟨K₂, hK₂B, hK₂le, fun d => ?_⟩
  obtain ⟨t, ht, hreg⟩ := hK₂ d
  refine ⟨t, ht, ?_⟩
  intro V _ _ ρ hρ hd f hf
  have hAd := standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
    ρ hρ
  obtain ⟨b, hb⟩ := (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ)
    (hmem J hJ)).exists_isStablePairing hAd
  -- the constant-term data, proved by induction on the span
  have hP : ∃ φ : standardLeviPoints i ν J → ℂ,
      IsRightFinite (standardComponentHom hA').range φ ∧ IsStandardConstantTerm hA' f φ ∧
      ∀ m ∈ rationalConstantTermThresholdRegion hG hi hν J t,
        f (m : rationalPoints G) =
          standardHalfModulus i ν J (minimalLeviInclusion hG hi hν J m) *
            φ (minimalLeviInclusion hG hi hν J m) := by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨v, hv, ℓ, hℓ, rfl⟩ := hg
      exact exists_constantTerm_data_of_region hG hi hν hB A q hA hmem ζ hζ hK0 hcover hJ hA'
        ρ hρ hb ℓ v (fun m hm => hreg ρ hρ b hb hd v hv ℓ hℓ m hm)
    | zero =>
      refine ⟨0, isRightFinite_zero _, isStandardConstantTerm_zero hA', fun m _ => ?_⟩
      simp
    | add f₁ f₂ _ _ h₁ h₂ =>
      obtain ⟨φ₁, hR₁, hC₁, hT₁⟩ := h₁
      obtain ⟨φ₂, hR₂, hC₂, hT₂⟩ := h₂
      refine ⟨φ₁ + φ₂, hR₁.add hR₂, hC₁.add hA' hC₂, fun m hm => ?_⟩
      simp only [Pi.add_apply, hT₁ m hm, hT₂ m hm, mul_add]
    | smul c f₁ _ h₁ =>
      obtain ⟨φ₁, hR₁, hC₁, hT₁⟩ := h₁
      refine ⟨c • φ₁, hR₁.smul c, hC₁.smul hA' c, fun m hm => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, hT₁ m hm]
      ring
  obtain ⟨φ, hR, hC, hT⟩ := hP
  intro m hm
  rw [standardConstantTerm_eq hi hζ' hA' hR hC]
  exact hT m hm

end Comparison

end Langlands.HarishChandraSchwartz
