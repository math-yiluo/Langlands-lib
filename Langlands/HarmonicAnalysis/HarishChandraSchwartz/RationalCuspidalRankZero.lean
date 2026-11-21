import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteCoefficientCuspLift
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalDiscreteUpper
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationRankZero
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound

/-! # Waldspurger VIII.4 in relative rank zero, and the upper inclusion from its inputs -/

noncomputable section

universe u uG uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct Pointwise

namespace Langlands.HarishChandraSchwartz

/-! ### Finite dimensionality from a finite double-coset cover -/

section Finite

variable {Γ : Type uG} [Group Γ]

/-- The functions `f` with `f(a g) = χ(a) f(g)` for `a ∈ A` and `f(g h) = f(g)` for `h ∈ H`. -/
def centralRightInvariantSubmodule (A H : Subgroup Γ) (χ : A →* ℂˣ) :
    Submodule ℂ (Γ → ℂ) where
  carrier := {f | (∀ (a : A) (g : Γ), f ((a : Γ) * g) = (χ a : ℂ) * f g) ∧
    ∀ h ∈ H, ∀ g : Γ, f (g * h) = f g}
  add_mem' := fun {f₁ f₂} h₁ h₂ =>
    ⟨fun a g => by simp only [Pi.add_apply, h₁.1 a g, h₂.1 a g, mul_add],
      fun h hh g => by simp only [Pi.add_apply, h₁.2 h hh g, h₂.2 h hh g]⟩
  zero_mem' := ⟨fun a g => by simp, fun h hh g => rfl⟩
  smul_mem' := fun c f hf =>
    ⟨fun a g => by simp only [Pi.smul_apply, smul_eq_mul, hf.1 a g]; ring,
      fun h hh g => by simp only [Pi.smul_apply, hf.2 h hh g]⟩

/-- If `Γ = A X H` for a finite set `X`, the functions that are `χ`-equivariant on the left
under `A` and invariant on the right under `H` form a finite-dimensional space: such a
function is determined by its values on `X`. -/
theorem finiteDimensional_centralRightInvariantSubmodule (A H : Subgroup Γ) (χ : A →* ℂˣ)
    (X : Finset Γ) (hX : ∀ g : Γ, ∃ a : A, ∃ x ∈ X, ∃ h ∈ H, g = (a : Γ) * x * h) :
    FiniteDimensional ℂ (centralRightInvariantSubmodule A H χ) := by
  let L : centralRightInvariantSubmodule A H χ →ₗ[ℂ] (X → ℂ) :=
    { toFun := fun f x => (f : Γ → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  apply Subtype.ext
  funext g
  obtain ⟨a, x, hx, h, hh, rfl⟩ := hX g
  have hfx : (f : Γ → ℂ) x = 0 := congrFun hf ⟨x, hx⟩
  rw [f.2.2 h hh, f.2.1 a x, hfx, mul_zero]
  rfl

/-- **A finite double-coset cover.** Let `N` be a compact normal subgroup, `A` a central
subgroup with `Γ ⧸ (N ⊔ A)` finite, and `H` an open subgroup. Then `Γ = A X H` for a finite
set `X`. -/
theorem exists_finset_eq_mul_mul [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N A H : Subgroup Γ) [N.Normal] (hA : A ≤ Subgroup.center Γ) [Finite (Γ ⧸ (N ⊔ A))]
    (hN : IsCompact (N : Set Γ)) (hH : IsOpen (H : Set Γ)) :
    ∃ X : Finset Γ, ∀ g : Γ, ∃ a : A, ∃ x ∈ X, ∃ h ∈ H, g = (a : Γ) * x * h := by
  classical
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hN (V := (H : Set Γ))
    (by rw [hH.interior_eq]; exact ⟨1, H.one_mem⟩)
  let : Fintype (Γ ⧸ (N ⊔ A)) := Fintype.ofFinite _
  refine ⟨Finset.image (fun p : (Γ ⧸ (N ⊔ A)) × Γ => Quotient.out p.1 * p.2⁻¹)
    (Finset.univ ×ˢ t), fun g => ?_⟩
  obtain ⟨⟨k, hk⟩, hw⟩ := QuotientGroup.mk_out_eq_mul (N ⊔ A) g
  have hk' : k⁻¹ ∈ ((N : Set Γ) * (A : Set Γ)) := by
    rw [← Subgroup.normal_mul]
    exact (N ⊔ A).inv_mem hk
  obtain ⟨n, hn, b, hb, hnb⟩ := hk'
  obtain ⟨z, hz, hzn⟩ := Set.mem_iUnion₂.mp (ht hn)
  set y := Quotient.out (QuotientGroup.mk g : Γ ⧸ (N ⊔ A)) with hy
  have hnb' : n * b = k⁻¹ := hnb
  have hg : g = y * n * b := by
    rw [mul_assoc, hnb', hw, mul_inv_cancel_right]
  refine ⟨⟨b, hb⟩, y * z⁻¹, Finset.mem_image.mpr ⟨(QuotientGroup.mk g, z),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩, z * n, hzn, ?_⟩
  have hbc : y * n * b = b * (y * n) :=
    Subgroup.mem_center_iff.mp (hA hb) (y * n)
  calc g = y * n * b := hg
    _ = b * (y * n) := hbc
    _ = ((⟨b, hb⟩ : A) : Γ) * (y * z⁻¹) * (z * n) := by
      simp only [mul_assoc, inv_mul_cancel_left]

end Finite

/-! ### Rapid decay on a compact subgroup -/

section Compact

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] {Ξ σ : Γ → ℝ}

/-- On a compact subgroup every continuous function decreases rapidly, for continuous
positive `Ξ` and continuous nonnegative `σ`. -/
theorem isRapidlyDecreasingOn_of_isCompact (hΞc : Continuous Ξ) (hΞ : ∀ g, 0 < Ξ g)
    (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) {N : Subgroup Γ} (hN : IsCompact (N : Set Γ))
    {f : Γ → ℂ} (hf : Continuous f) : IsRapidlyDecreasingOn Ξ σ N f := by
  intro r
  have hb : ∀ g, (0 : ℝ) < 1 + σ g := fun g => by linarith [hσ g]
  have hw : ∀ g, 0 < Ξ g * (1 + σ g) ^ (-r) := fun g =>
    mul_pos (hΞ g) (Real.rpow_pos_of_pos (hb g) _)
  have hc : Continuous fun g => ‖f g‖ / (Ξ g * (1 + σ g) ^ (-r)) :=
    hf.norm.div (hΞc.mul ((continuous_const.add hσc).rpow_const fun g => Or.inl (hb g).ne'))
      fun g => (hw g).ne'
  obtain ⟨c, hc'⟩ := (hN.image hc).bddAbove
  refine ⟨c, fun n hn => ?_⟩
  have h1 := hc' ⟨n, hn, rfl⟩
  rw [div_le_iff₀ (hw n)] at h1
  calc ‖f n‖ ≤ c * (Ξ n * (1 + σ n) ^ (-r)) := h1
    _ = c * Ξ n * (1 + σ n) ^ (-r) := by ring

variable [IsTopologicalGroup Γ]

/-- On a compact subgroup the coefficients of every smooth representation decrease rapidly. -/
theorem hasRapidlyDecreasingCoefficientsOn_of_isCompact (hΞc : Continuous Ξ)
    (hΞ : ∀ g, 0 < Ξ g) (hσc : Continuous σ) (hσ : ∀ g, 0 ≤ σ g) {N : Subgroup Γ}
    (hN : IsCompact (N : Set Γ)) (A : SmoothRep.{0, uG, uV} ℂ Γ) :
    HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation := by
  intro v ℓ
  have h : (fun g => ℓ.val (A.representation g v)) =
      ⇑(Plancherel.coefficientTensorMap A (v ⊗ₜ[ℂ] ℓ)) :=
    funext fun g => (Plancherel.coefficientTensorMap_tmul A v ℓ g).symm
  rw [h]
  exact isRapidlyDecreasingOn_of_isCompact hΞc hΞ hσc hσ hN
    (Plancherel.coefficientTensorMap A _).continuous

end Compact

/-! ### Rational points -/

section Rational

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily
open DiscreteCoefficientCuspLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalDecaySecondCountable
  rationalDecayT2 rationalDecayNonarchimedean

/-! #### The upper inclusion from its weight inputs -/

/-- **The upper inclusion of VIII.4.2 from the structural data and finite level spans.** For a
compact open `K0` with the simultaneous standard basis and the finite Cartan covering (the
structural inputs of Lemma II.1.5), the published upper step
`rationalCuspidalDiscreteUpperEstimate` applies with the central weights of
`rationalSplitCenterHeight` and the `L²` weights of `rationalXiUpperBound`: if all level spans
are finite dimensional, the raw image lies in the discrete-series coefficient sum. -/
theorem rationalCuspidalCentralImage_subset_of_specialCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range)
    [muA.IsHaarMeasure] :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
      (∀ J : OpenSubgroup (rationalPoints G), IsCompact (J : Set (rationalPoints G)) →
        FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ J.toSubgroup)) →
      rationalCuspidalCentralImage hKc hPK ρ muA χ ⊆
        (discreteSeriesCentralCoefficientSpace.{u, max u uV}
          (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
          mu χ : Set (rationalPoints G → ℂ)) := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu hfinite
  let muG : Measure (rationalPoints G) := Measure.haar
  have hw := RationalSplitCenterHeightStatement.centralWeights K.isOpen hKc hPK ρ
    rationalSplitCenterHeight hG hs hρ muA
  have hL := RationalXiSquareIntegrableStatement.l2Weights
    (rationalXiSquareIntegrable_of_upperBound rationalXiUpperBound) hG hi hν hK0o hK0c hbasis
    hcover (K := K.toSubgroup) K.isOpen hKc hPK hρ muG
  exact rationalCuspidalDiscreteUpperEstimate.{u, uV} F G hG S i hi ν hν K hKc hPK N ρ hρ T s
    hs muA muG hw hL mu χ hχ hu hfinite

/-! #### Relative rank zero -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Without simple relative roots, the maximal split torus is central and the radical of the
minimal standard parabolic subgroup is trivial. -/
theorem rankZero_isCentral_unipotent_eq_bot (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (h0 : simpleRelativeRoots i ν = ∅) :
    IsCentral i ∧ standardUnipotentPoints i ν ∅ = ⊥ := by
  have h := standardParabolicEndpoints F G hG S i hi ν hν
  have hZ : torusCentralizer i = ⊤ := h.2.1.symm.trans (by simpa only [h0] using h.2.2.2.1)
  have hU : standardUnipotent i ν ∅ = ⊥ := by simpa only [h0] using h.2.2.2.2
  refine ⟨(isCentral_iff_torusCentralizer_eq_top i).mpr hZ, ?_⟩
  change (standardUnipotent i ν ∅).carrier _ = _
  rw [hU]
  rfl

/-- Without simple relative roots, `Ξ = 1`: the modulus of the minimal parabolic subgroup is
trivial because its radical is. -/
theorem rationalXi_eq_one_of_simpleRoots_empty (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (h0 : simpleRelativeRoots i ν = ∅) {K : OpenSubgroup (rationalPoints G)}
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup) (g : rationalPoints G) :
    rationalXi hKc hPK g = 1 := by
  have hU := (rankZero_isCentral_unipotent_eq_bot hG hi hν h0).2
  have hmod (p : standardParabolicPoints i ν ∅) : rationalMinimalModulus i ν p = 1 := by
    apply closedNormalizerCharacter_eq_one_of_commute _ (isClosed_standardUnipotentPoints i ν ∅)
    intro u hu
    rw [hU, Subgroup.mem_bot] at hu
    simp [hu]
  simp [rationalXi, xi, iwasawaWeight, hmod]

omit [LocallyOfFiniteType G.X.hom] in
/-- Without simple relative roots, `G¹` is compact. -/
theorem isCompact_rationalCommonNormKernel_of_simpleRoots_empty (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (h0 : simpleRelativeRoots i ν = ∅) :
    IsCompact (rationalCommonNormKernel G : Set (rationalPoints G)) :=
  BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit
    centralQuotientReductive anisotropicCompactness_proof G hG hi
    (rankZero_isCentral_unipotent_eq_bot hG hi hν h0).1

/-- **Finite level spans in rank zero (Proposition VIII.4.1, finiteness).** Without simple
relative roots, `G = A_G(F) X H` for a finite `X`, so every actual central level span is
finite dimensional: each `p_χ(φ)` is `χ`-equivariant under `A_G(F)` and right `H`-invariant. -/
theorem finiteDimensional_rationalCuspidalCentralLevelSpan_of_simpleRoots_empty
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (h0 : simpleRelativeRoots i ν = ∅) {K : OpenSubgroup (rationalPoints G)}
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range)
    [muA.IsHaarMeasure] (χ : (rationalPoints.map s).range →* ℂˣ)
    (H : OpenSubgroup (rationalPoints G)) :
    FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) := by
  have : BorelSpace (rationalPoints.map s).range := Subtype.borelSpace _
  have : MeasurableMul (rationalPoints.map s).range :=
    ⟨fun c => (continuous_const.mul continuous_id).measurable,
      fun c => (continuous_id.mul continuous_const).measurable⟩
  have hZc := hs.isCentralSplitTorus.isCentral.range_le_center
  have : muA.IsMulRightInvariant := by
    constructor
    intro a
    have he :
        (fun x : (rationalPoints.map s).range => x * a) = (fun x => a * x) := by
      funext x
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc a.property) x)
    rw [he, map_mul_left_eq_self]
  have : Finite (rationalPoints G ⧸
      (rationalCommonNormKernel G ⊔ (rationalPoints.map s).range)) :=
    finite_rationalCentralQuotient s hs.isCentralSplitTorus.isCentral
      (finiteIndex_splitValuationImage_of_isSplitComponent hG s hs)
  obtain ⟨X, hX⟩ := exists_finset_eq_mul_mul (rationalCommonNormKernel G)
    (rationalPoints.map s).range H.toSubgroup hZc
    (isCompact_rationalCommonNormKernel_of_simpleRoots_empty hG hi hν h0) H.isOpen
  have := finiteDimensional_centralRightInvariantSubmodule (rationalPoints.map s).range
    H.toSubgroup χ X hX
  refine Submodule.finiteDimensional_of_le (S₂ := centralRightInvariantSubmodule
    (rationalPoints.map s).range H.toSubgroup χ) (Submodule.span_le.mpr ?_)
  rintro _ ⟨φ, hφ, rfl⟩
  refine ⟨fun a g => centralProjection_mul_left _ a g, fun h hh g => ?_⟩
  have hbi : IsBiInvariant H.toSubgroup (φ : rationalPoints G → ℂ) := hφ.2
  have := IsBiInvariant.centralProjection (μA := muA) hZc hbi χ 1 H.toSubgroup.one_mem h hh g
  simpa only [one_mul] using this

/-- **The direct cusp lift in rank zero.** Without simple relative roots, every coefficient `f`
of a smooth representation on which `A_G(F)` acts by `χ` is `p_χ(φ)` for a Schwartz function
`φ`, automatically cuspidal, that is bi-invariant under every compact subgroup under which `f`
is. As in `exists_cuspidal_lift`, `φ = m⁻¹ f c` with `c` the transversal cutoff on
`G(F) ⧸ G¹` and `m = μ_A(A_G(F) ∩ G¹)`; here `G¹` is compact, so the coefficients decrease
rapidly on `G¹` and no square integrability is needed. -/
theorem exists_cuspidal_lift_of_simpleRoots_empty (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (h0 : simpleRelativeRoots i ν = ∅) {K : OpenSubgroup (rationalPoints G)}
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range)
    [muA.IsHaarMeasure] (χ : (rationalPoints.map s).range →* ℂˣ)
    (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G))
    (hχA : ∀ (a : (rationalPoints.map s).range) (v : A),
      A.representation (a : rationalPoints G) v = (χ a : ℂ) • v) :
    ∀ f ∈ coefficientFunctionSpace A, ∃ φ : RationalSchwartzSpace hKc hPK ρ,
      φ ∈ rationalCuspidalSubmodule hKc hPK ρ ∧
      centralProjection muA χ (φ : rationalPoints G → ℂ) = f ∧
      ∀ H : Subgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
        IsBiInvariant H f → IsBiInvariant H (φ : rationalPoints G → ℂ) := by
  intro f hf
  have : BorelSpace (rationalPoints.map s).range := Subtype.borelSpace _
  have : MeasurableMul (rationalPoints.map s).range :=
    ⟨fun c => (continuous_const.mul continuous_id).measurable,
      fun c => (continuous_id.mul continuous_const).measurable⟩
  have hZc := hs.isCentralSplitTorus.isCentral.range_le_center
  have hfZ := coefficientFunctionSpace_mul_left _ χ A hχA hf
  have hf' : f ∈ (LinearMap.range (coefficientTensorMap A)).map (LocallyConstant.coeFnₗ ℂ) :=
    coefficientFunctionSpace_eq_map A ▸ hf
  obtain ⟨f₀, ⟨t, rfl⟩, rfl⟩ := hf'
  have hD : HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK)
      (rationalHeight (F := F) ρ) (rationalCommonNormKernel G) A.representation :=
    hasRapidlyDecreasingCoefficientsOn_of_isCompact (continuous_rationalXi K.isOpen hKc hPK)
      (rationalXi_pos K.isOpen hKc hPK) (continuous_rationalHeight ρ) (rationalHeight_nonneg ρ)
      (isCompact_rationalCommonNormKernel_of_simpleRoots_empty hG hi hν h0) A
  have : Finite (rationalPoints G ⧸
      (rationalCommonNormKernel G ⊔ (rationalPoints.map s).range)) :=
    finite_rationalCentralQuotient s hs.isCentralSplitTorus.isCentral
      (finiteIndex_splitValuationImage_of_isSplitComponent hG s hs)
  have hc := hasCompactSupport_transversalCutoff (rationalCommonNormKernel G)
    (rationalPoints.map s).range (isOpen_rationalCommonNormKernel G)
  have hmem := mul_mem_rationalSchwartz K.isOpen hKc hPK ρ hD
    (f := coefficientTensorMap A t) ⟨t, rfl⟩ hc
  have hm := (centralNormKernelMass_pos hG hs muA).ne'
  let φ₀ : RationalSchwartzSpace hKc hPK ρ := (⟨_, hmem⟩ : schwartzSubmodule _ _)
  refine ⟨((muA.real ((rationalCommonNormKernel G).comap
    (rationalPoints.map s).range.subtype : Set (rationalPoints.map s).range) : ℂ)⁻¹) • φ₀,
    ?_, ?_, ?_⟩
  · rw [rationalCuspidalSubmodule_eq_top_of_simpleRoots_empty hKc hPK ρ h0]
    exact Submodule.mem_top
  · rw [Space.coe_smul]
    exact centralProjection_smul_mul_transversalCutoff _ _ hZc
      (isOpen_rationalCommonNormKernel G) muA χ hfZ hm
  · intro H hH hfH
    rw [Space.coe_smul]
    exact (isBiInvariant_mul_quotient _ (compactSubgroup_le_rationalCommonNormKernel G H hH)
      hfH _).smul _

end Rational

/-! ### Statements and assembly -/

section Statements

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Aubert.General

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The inclusion `⊆` of Theorem VIII.4.2: the raw central-integral image of the actual
cuspidal Schwartz space lies in the canonical discrete-series coefficient sum. The binders
are those of `RationalCuspidalDiscreteCoefficientStatement`. -/
def RationalCuspidalDiscreteCoefficientUpperInclusionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
        rationalCuspidalCentralImage hKc hPK ρ muA χ ⊆
          (discreteSeriesCentralCoefficientSpace.{u, max u uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ : Set (rationalPoints G → ℂ))

/-- **The upper inclusion from the joint special-compact data and VIII.4.1.** The structural
data of `JointSpecialCompactBasisExistenceStatement` and the finiteness of
`RationalCuspidalCentralProjectionFiniteStatement` give the inclusion `⊆` of VIII.4.2. -/
theorem rationalCuspidalDiscreteCoefficientUpperInclusion_of_joint
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hfinite : RationalCuspidalCentralProjectionFiniteStatement.{u}) :
    RationalCuspidalDiscreteCoefficientUpperInclusionStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu
  obtain ⟨K0, hK0o, hK0c, -, hbasis, hcover, -⟩ :=
    exists_constantTermPremises_of_joint hJoint hG hi hν
  exact rationalCuspidalCentralImage_subset_of_specialCompact.{u, uV} hG hi hν hK0o hK0c hbasis
    hcover hKc hPK ρ hρ hs muA mu χ hχ hu
    (fun J hJ => (hfinite F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχ hu J hJ).2)

/-- **Theorem VIII.4.2 from its two inclusions.** The upper inclusion together with the lower
inclusion at the carrier universe `max u uV` is the published equality. -/
theorem rationalCuspidalDiscreteCoefficient_of_inclusions
    (hupper : RationalCuspidalDiscreteCoefficientUpperInclusionStatement.{u, uV})
    (hlower : RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, max u uV}) :
    RationalCuspidalDiscreteCoefficientStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu
  exact Set.Subset.antisymm
    (hupper F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA mu χ hχ hu)
    (hlower F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA mu χ hχ hu)

/-- **Theorem VIII.4.2 from three open premises.** The joint special-compact data, radical
convergence of all Schwartz functions, and the finiteness of VIII.4.1 give the published
equality. -/
theorem rationalCuspidalDiscreteCoefficient_of_joint
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hconv : RationalSchwartzConstantTermConvergenceStatement.{u})
    (hfinite : RationalCuspidalCentralProjectionFiniteStatement.{u}) :
    RationalCuspidalDiscreteCoefficientStatement.{u, uV} :=
  rationalCuspidalDiscreteCoefficient_of_inclusions
    (rationalCuspidalDiscreteCoefficientUpperInclusion_of_joint hJoint hfinite)
    (DiscreteCoefficientCuspLift.rationalCuspidalDiscreteCoefficientLowerInclusion_of_joint
      hJoint hconv)

/-- Proposition VIII.4.1 for groups without simple relative roots: the binders of
`RationalCuspidalCentralProjectionFiniteStatement` with `simpleRelativeRoots i ν = ∅`. -/
def RationalCuspidalCentralProjectionFiniteRankZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν → simpleRelativeRoots i ν = ∅ →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G), IsSplitComponent s →
    ∀ (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
    ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
      (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup :
        Set (rationalPoints G → ℂ)) =
          rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup ∧
      FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup)

theorem rationalCuspidalCentralProjectionFiniteRankZero :
    RationalCuspidalCentralProjectionFiniteRankZeroStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν h0 K hKc hPK N _ ρ hρ T s hs muA _ χ hχ hu H _
  refine ⟨?_, finiteDimensional_rationalCuspidalCentralLevelSpan_of_simpleRoots_empty hG hi hν
    h0 hKc hPK ρ hs muA χ H⟩
  have hc : CentralIntegralConvergesOn (rationalCuspidalLevel hKc hPK ρ H.toSubgroup) muA χ :=
    fun φ _ g => rationalSchwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs
      muA χ hχ hu φ Submodule.mem_top g
  exact coe_schwartzCentralIntegralSpan_eq_image _ _ _ hc

/-- The level-preserving lifting of VIII.5 for groups without simple relative roots: the
binders of `RationalCuspidalFixedCoefficientLiftingStatement` with
`simpleRelativeRoots i ν = ∅`. -/
def RationalCuspidalFixedCoefficientLiftingRankZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν → simpleRelativeRoots i ν = ∅ →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
      ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
      ∀ ω ∈ discreteSeriesCentralFixed.{u, uV} (rationalPoints.map s).range
        hs.isCentralSplitTorus.isCentral.range_le_center mu χ H.toSubgroup,
      ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H.toSubgroup f →
        f ∈ rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup

theorem rationalCuspidalFixedCoefficientLiftingRankZero :
    RationalCuspidalFixedCoefficientLiftingRankZeroStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν h0 K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu H hH ω hω f hf hHf
  have hχA : ∀ (a : (rationalPoints.map s).range) (v : ω.val.out.obj),
      ω.val.out.obj.representation (a : rationalPoints G) v = (χ a : ℂ) • v := by
    have h := hω.1
    rw [← Quotient.out_eq ω.val] at h
    exact h
  obtain ⟨φ, hφ, hφf, hφH⟩ := exists_cuspidal_lift_of_simpleRoots_empty hG hi hν h0 hKc hPK ρ
    hs muA χ ω.val.out.obj hχA f hf
  exact ⟨φ, ⟨hφ, hφH H.toSubgroup hH hHf⟩, hφf⟩

/-- The inclusion `⊇` of VIII.4.2 for groups without simple relative roots: the binders of
`RationalCuspidalDiscreteCoefficientLowerInclusionStatement` with
`simpleRelativeRoots i ν = ∅`. -/
def RationalCuspidalDiscreteCoefficientLowerInclusionRankZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν → simpleRelativeRoots i ν = ∅ →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
        (discreteSeriesCentralCoefficientSpace.{u, uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ : Set (rationalPoints G → ℂ)) ⊆
          rationalCuspidalCentralImage hKc hPK ρ muA χ

theorem rationalCuspidalDiscreteCoefficientLowerInclusionRankZero :
    RationalCuspidalDiscreteCoefficientLowerInclusionRankZeroStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν h0 K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu
  have hc : CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ :=
    fun φ _ g => rationalSchwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs
      muA χ hχ hu φ Submodule.mem_top g
  have hspan := coe_schwartzCentralIntegralSpan_eq_image _ _ _ hc
  have hle : discreteSeriesCentralCoefficientSpace.{u, uV} (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center mu χ ≤
        schwartzCentralIntegralSpan (rationalCuspidalSubmodule hKc hPK ρ) muA χ := by
    refine (discreteSeriesCentralCoefficientSpace_le_iff _ _ _ _ _).mpr ?_
    intro ω hω f hf
    have hχA : ∀ (a : (rationalPoints.map s).range) (v : ω.val.out.obj),
        ω.val.out.obj.representation (a : rationalPoints G) v = (χ a : ℂ) • v := by
      have h := hω
      rw [← Quotient.out_eq ω.val] at h
      exact h
    obtain ⟨φ, hφ, hφf, -⟩ := exists_cuspidal_lift_of_simpleRoots_empty hG hi hν h0 hKc hPK ρ
      hs muA χ ω.val.out.obj hχA f hf
    exact Submodule.subset_span ⟨φ, hφ, hφf⟩
  intro f hf
  exact (Set.ext_iff.mp hspan f).mp (hle hf)

/-- **Theorem VIII.4.2 for groups without simple relative roots**: the binders of
`RationalCuspidalDiscreteCoefficientStatement` with `simpleRelativeRoots i ν = ∅`. -/
def RationalCuspidalDiscreteCoefficientRankZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν → simpleRelativeRoots i ν = ∅ →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
        rationalCuspidalCentralImage hKc hPK ρ muA χ =
          (discreteSeriesCentralCoefficientSpace.{u, max u uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ : Set (rationalPoints G → ℂ))

theorem rationalCuspidalDiscreteCoefficientRankZero :
    RationalCuspidalDiscreteCoefficientRankZeroStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν h0 K hKc hPK N _ ρ hρ T s hs muA _
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu
  refine Set.Subset.antisymm ?_
    (rationalCuspidalDiscreteCoefficientLowerInclusionRankZero.{u, max u uV} F G hG S i hi ν hν
      h0 K hKc hPK N ρ hρ T s hs muA mu χ hχ hu)
  let muG : Measure (rationalPoints G) := Measure.haar
  have hw := RationalSplitCenterHeightStatement.centralWeights K.isOpen hKc hPK ρ
    rationalSplitCenterHeight hG hs hρ muA
  have hL := rationalL2Weights K.isOpen hKc hPK ρ
    (rationalSquareIntegrableWeight_of_compact_normKernel hG
      (isCompact_rationalCommonNormKernel_of_simpleRoots_empty hG hi hν h0) ρ hρ muG
      (Ξ := rationalXi hKc hPK) (A := 1) (fun g => by
        rw [rationalXi_eq_one_of_simpleRoots_empty hG hi hν h0 hKc hPK, abs_one]))
  exact rationalCuspidalDiscreteUpperEstimate.{u, uV} F G hG S i hi ν hν K hKc hPK N ρ hρ T s
    hs muA muG hw hL mu χ hχ hu fun J _ =>
      finiteDimensional_rationalCuspidalCentralLevelSpan_of_simpleRoots_empty hG hi hν h0 hKc
        hPK ρ hs muA χ J

end Statements

end Langlands.HarishChandraSchwartz
