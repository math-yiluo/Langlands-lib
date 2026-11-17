import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecayProof
import Langlands.Representation.Plancherel.RationalCentralQuotient

/-! # Extending norm-kernel coefficient bounds across a finite central quotient -/

noncomputable section

open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (c : UnitaryCentralCharacter ρ)
  (N A : Subgroup G) [N.Normal] [A.Normal]
  (hA : A ≤ Subgroup.center G) [Finite (G ⧸ (N ⊔ A))]
  (Ξ : G → ℝ) (hΞ : ∀ g, 0 ≤ Ξ g)
  (hΞA : ∀ (a : G), a ∈ A → ∀ g, Ξ (g * a) = Ξ g)
  (htrans : UniformTranslationBound Ξ)

include c hA hΞ hΞA htrans in
/-- Bounds on every norm-kernel coefficient extend globally when the residual
quotient is finite and the coefficient norm and Xi are invariant under its central factor. -/
theorem hasXiBoundedCoefficients_of_finite_central_quotient
    (hN : ∀ (v : V) (ℓ : SmoothDual ρ), ∃ C : ℝ,
      ∀ n ∈ N, ‖ℓ.val (ρ n v)‖ ≤ C * Ξ n) : HasXiBoundedCoefficients Ξ ρ := by
  classical
  let := Fintype.ofFinite (G ⧸ (N ⊔ A))
  let H := N ⊔ A
  let t : G ⧸ H → G := fun j => j.out
  intro v ℓ
  choose C hC using fun j : G ⧸ H => hN (ρ (t j) v) ℓ
  choose D hD using fun j : G ⧸ H => htrans 1 (t j)⁻¹
  let B : G ⧸ H → ℝ := fun j => max (C j) 0 * max (D j) 0
  have hB (j : G ⧸ H) : 0 ≤ B j := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨1 + ∑ j, B j, by positivity, fun g => ?_⟩
  let j : G ⧸ H := QuotientGroup.mk g
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_out_eq_mul H g
  have ht : t j = g * n₀ := hn₀
  have hn₀H : (n₀ : G)⁻¹ ∈ N ⊔ A := H.inv_mem n₀.property
  obtain ⟨n, hn, a, ha, hna⟩ := Subgroup.mem_sup_of_normal_right.mp hn₀H
  let n' : G := t j * n * (t j)⁻¹
  have hn' : n' ∈ N := Subgroup.Normal.conj_mem inferInstance n hn (t j)
  have hg : g = n' * t j * a := by
    have hg' : g = t j * (n₀ : G)⁻¹ := by rw [ht]; group
    rw [hg', ← hna]
    dsimp [n']
    group
  have hnorm : ‖ℓ.val (ρ g v)‖ = ‖ℓ.val (ρ n' (ρ (t j) v))‖ := by
    change ‖matrixCoefficient ρ ℓ.val v g‖ = _
    rw [hg, c.norm_matrixCoefficient_mul_center ℓ.val v (n' * t j) ⟨a, hA ha⟩]
    change ‖ℓ.val (ρ (n' * t j) v)‖ = _
    rw [map_mul, Module.End.mul_apply]
  have hweight : Ξ n' ≤ max (D j) 0 * Ξ g := by
    have hd := hD j (n' * t j)
    simp only [one_mul, mul_inv_cancel_right] at hd
    have he : Ξ (n' * t j) = Ξ g := by rw [hg, hΞA a ha]
    rw [he] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞ g))
  calc ‖ℓ.val (ρ g v)‖ = ‖ℓ.val (ρ n' (ρ (t j) v))‖ := hnorm
    _ ≤ C j * Ξ n' := hC j n' hn'
    _ ≤ max (C j) 0 * Ξ n' := mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞ n')
    _ ≤ max (C j) 0 * (max (D j) 0 * Ξ g) :=
      mul_le_mul_of_nonneg_left hweight (le_max_right _ _)
    _ = B j * Ξ g := by dsimp [B]; ring
    _ ≤ (∑ i, B i) * Ξ g := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j)) (hΞ g)
    _ ≤ (1 + ∑ i, B i) * Ξ g := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (by norm_num)) (hΞ g)

/-- A positive constant extending the coefficient bound from the norm kernel;
its definition retains the original coefficient and weights. -/
def finiteCentralCoefficientConstant
    (hN : ∀ (v : V) (ℓ : SmoothDual ρ), ∃ C : ℝ,
      ∀ n ∈ N, ‖ℓ.val (ρ n v)‖ ≤ C * Ξ n) (v : V) (ℓ : SmoothDual ρ) : ℝ :=
  Classical.choose (hasXiBoundedCoefficients_of_finite_central_quotient
    ρ c N A hA Ξ hΞ hΞA htrans hN v ℓ)

/-- The chosen positive constant bounds the original coefficient at every group point. -/
theorem finiteCentralCoefficientConstant_spec
    (hN : ∀ (v : V) (ℓ : SmoothDual ρ), ∃ C : ℝ,
      ∀ n ∈ N, ‖ℓ.val (ρ n v)‖ ≤ C * Ξ n) (v : V) (ℓ : SmoothDual ρ) :
    0 < finiteCentralCoefficientConstant ρ c N A hA Ξ hΞ hΞA htrans hN v ℓ ∧
      ∀ g, ‖ℓ.val (ρ g v)‖ ≤
        finiteCentralCoefficientConstant ρ c N A hA Ξ hΞ hΞA htrans hN v ℓ * Ξ g :=
  Classical.choose_spec (hasXiBoundedCoefficients_of_finite_central_quotient
    ρ c N A hA Ξ hΞ hΞA htrans hN v ℓ)

include c hA hΞ hΞA htrans in
/-- Only order zero of rapid norm-kernel decay is required for the global Xi bound. -/
theorem hasXiBoundedCoefficients_of_rapid_on_finite_central_quotient (σ : G → ℝ)
    (hrapid : HasRapidlyDecreasingCoefficientsOn Ξ σ N ρ) : HasXiBoundedCoefficients Ξ ρ := by
  apply hasXiBoundedCoefficients_of_finite_central_quotient ρ c N A hA Ξ hΞ hΞA htrans
  intro v ℓ
  obtain ⟨C, hC⟩ := hrapid v ℓ 0
  exact ⟨C, fun n hn => by simpa only [neg_zero, Real.rpow_zero, mul_one] using hC n hn⟩

end Langlands.HarishChandraSchwartz



open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

universe u

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance centralExtensionSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance centralExtensionT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance centralExtensionNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Langlands.Plancherel.rationalPoints_nonarchimedeanGroup G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}

include hKo in
/-- The original finite-index split-valuation premise supplies precisely the
finite central quotient needed to extend rapid norm-kernel decay globally. -/
theorem hasXiBoundedCoefficients_of_rationalNormKernel
    (hs : IsCentral s) (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (rationalPoints G) V) (c : UnitaryCentralCharacter π)
    (σ : rationalPoints G → ℝ)
    (hrapid : HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) σ
      (rationalCommonNormKernel G) π) :
    HasXiBoundedCoefficients (rationalXi hKc hPK) π := by
  let := (rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  let := finite_rationalCentralQuotient s hs hindex
  apply hasXiBoundedCoefficients_of_rapid_on_finite_central_quotient
    π c (rationalCommonNormKernel G) (rationalPoints.map s).range hs.range_le_center
    (rationalXi hKc hPK) (rationalXi_nonneg hKc hPK) ?_
    (rationalXi_uniformTranslationBound hKo hKc hPK) σ hrapid
  intro a ha g
  have hc := Subgroup.mem_center_iff.mp (hs.range_le_center ha) g
  rw [hc]
  exact rationalXi_mul_of_mem_range hKo hKc hPK hs ha g

include hKo in
/-- Applying the published rational square-integrable decay theorem gives the
global coefficient Xi input, under its retained structural premises. -/
theorem hasXiBoundedCoefficients_of_rationalSquareIntegrable
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt i ν K0)
    (hcover : Langlands.Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    (ρ : MatrixRepresentation G Idx) (hs : IsSplitComponent s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : MeasureTheory.Measure (rationalPoints G ⧸ (rationalPoints.map s).range))
      [mu.IsHaarMeasure] (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
        hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      HasXiBoundedCoefficients (rationalXi hKc hPK) A.representation := by
  intro mu hmu A hsq
  obtain ⟨c, hc⟩ := hsq.2
  exact hasXiBoundedCoefficients_of_rationalNormKernel hKo hKc hPK
    hs.isCentralSplitTorus.isCentral hindex A.representation c (rationalHeight (F := F) ρ)
    (hasRapidlyDecreasingCoefficientsOn_of_squareIntegrable hKo hKc hPK hG hi hν
      hK0c hbasis hcover ρ hs mu A hsq)

end Rational

end Langlands.HarishChandraSchwartz
