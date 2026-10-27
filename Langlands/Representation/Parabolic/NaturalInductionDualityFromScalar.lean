import Langlands.Representation.Parabolic.NaturalInductionDualityStatement
import Langlands.Representation.Induction.CompactScalarStatement
import Langlands.Representation.Induction.CompactPairingDuality
import Langlands.Representation.Induction.PiScalarIntegral
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Geometric.FlattenedLevi

/-!
# Natural induction duality from the GL scalar compact integral

The compact-picture pairing identifies the smooth dual of a normalized induced
representation with the normalized induction of the smooth dual, naturally in
the inducing representation, for standard GL parabolics and for refined
parabolics of product Levis, once the scalar compact integral is available for
standard GL parabolics.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- The general linear group of rank zero is trivial. -/
theorem generalLinear_zero_subsingleton (R : Type*) [CommRing R] :
    Subsingleton (GeneralLinear 0 R) :=
  ⟨fun _ _ => Units.ext (Matrix.ext fun i _ => i.elim0)⟩

section Scalar

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Compact scalar data for every standard block parabolic in every rank, rank
zero included: a compact subgroup with a Borel probability measure charging
nonempty open sets, whose average of every locally constant scalar function
covariant by the full modulus is invariant under right translation. -/
theorem exists_compactScalarData (hGL : GLParabolicCompactScalarIntegralStatement.{uF})
    {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∃ K : Subgroup (GeneralLinear n F.Carrier), CompactSpace K ∧
      (letI : MeasurableSpace K := borel K
       ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsOpenPosMeasure ∧
         ∀ φ : GeneralLinear n F.Carrier → ℂ, IsLocallyConstant φ →
           (∀ (q : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier),
             φ ((q : GeneralLinear n F.Carrier) * x) =
               (((T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0) : ℝ) : ℂ) * φ x) →
           ∀ g : GeneralLinear n F.Carrier,
             Integrable (fun k : K => φ ((k : GeneralLinear n F.Carrier) * g)) μ ∧
             (∫ k : K, φ ((k : GeneralLinear n F.Carrier) * g) ∂μ) =
               ∫ k : K, φ (k : GeneralLinear n F.Carrier) ∂μ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := generalLinear_zero_subsingleton F.Carrier
    have : Subsingleton (⊤ : Subgroup (GeneralLinear 0 F.Carrier)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have : Finite (⊤ : Subgroup (GeneralLinear 0 F.Carrier)) := Finite.of_subsingleton
    refine ⟨⊤, Finite.compactSpace, ?_⟩
    let : MeasurableSpace (⊤ : Subgroup (GeneralLinear 0 F.Carrier)) := borel _
    refine ⟨Measure.dirac 1, inferInstance, ⟨fun U _ hU => ?_⟩, fun φ _ _ g => ?_⟩
    · obtain ⟨x, hx⟩ := hU
      rw [Measure.dirac_apply_of_mem (Subsingleton.elim x 1 ▸ hx)]
      exact one_ne_zero
    · have hg : g = 1 := Subsingleton.elim _ _
      subst hg
      simp only [mul_one, and_true]
      have hconst : (fun k : (⊤ : Subgroup (GeneralLinear 0 F.Carrier)) =>
          φ (k : GeneralLinear 0 F.Carrier)) = fun _ => φ 1 :=
        funext fun k => congrArg φ (Subsingleton.elim _ _)
      rw [hconst]
      exact integrable_const _
  · obtain ⟨K, hKc, -, hμ⟩ := hGL p F T n hn B
    let : MeasurableSpace K := borel K
    obtain ⟨μ, hHaar, hprob, hscalar⟩ := hμ
    exact ⟨K.toSubgroup, isCompact_iff_compactSpace.mp hKc, μ, hprob,
      hHaar.toIsOpenPosMeasure, hscalar⟩

end Scalar

/-- The standard clause of natural induction duality follows from the scalar
compact integral for standard GL parabolics. -/
theorem standardNaturalInductionDuality_of_scalar
    (hGL : GLParabolicCompactScalarIntegralStatement.{uF}) :
    StandardNaturalInductionDualityClause.{uF, uV} := by
  intro p _ F T
  let := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  intro n B
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  have := T.generalLinearNonarchimedean n
  have := T.generalLinearLocallyCompactSpace n
  have := T.leviNonarchimedean B
  have := T.leviLocallyCompactSpace B
  have hdata := exists_compactScalarData T hGL B
  obtain ⟨K, -, hK⟩ := hdata
  let : MeasurableSpace K := borel K
  obtain ⟨μ, -, hpos, hscalar⟩ := hK
  let δ : B.parabolic F.Carrier → ℝ≥0 := fun q =>
    (T.leviModulus B (B.leviProjection F.Carrier q) : ℝ≥0)
  have hm : Continuous (B.leviProjection F.Carrier) := (T.blockLeviProjection B).continuous
  have hδ : ∀ q : B.parabolic F.Carrier,
      (T.parabolicHalfModulus B q : ℂ) * T.parabolicHalfModulus B q = ((δ q : ℝ) : ℂ) := by
    intro q
    have h := congrArg Units.val (T.leviHalfModulus_sq B (B.leviProjection F.Carrier q))
    rw [Units.val_pow_eq_pow_val, Jacquet.complexCharacter_apply, sq] at h
    exact h
  have hcofM : ∀ H : OpenSubgroup (B.Levi F.Carrier), ∃ L : OpenSubgroup (B.Levi F.Carrier),
      IsCompact (L : Set (B.Levi F.Carrier)) ∧ L ≤ H := by
    intro H
    obtain ⟨L, hL, hLH⟩ :=
      compactOpenSubgroupBasis (B.Levi F.Carrier) (H : Set (B.Levi F.Carrier)) H.mem_nhds_one
    exact ⟨L, hL, fun x hx => hLH hx⟩
  have hex := fun (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) (hσ : IsAdmissible σ.ρ) =>
    Induction.exists_integralDualEquiv (B.parabolic F.Carrier) (B.leviProjection F.Carrier)
      (T.parabolicHalfModulus B) δ K μ hm (T.isOpen_ker_parabolicHalfModulus B) hδ hcofM
      hscalar σ.ρ hσ.1 (normalizedInductionAdmissibility F T B _ σ.ρ hσ)
  refine ⟨fun σ hσ => Classical.choose (hex σ hσ), ?_⟩
  intro σ τ hσ hτ a ℓ
  exact Induction.integralDualEquiv_natural (B.parabolic F.Carrier) (B.leviProjection F.Carrier)
    (T.parabolicHalfModulus B) K μ σ.ρ τ.ρ _ _ (Classical.choose_spec (hex σ hσ))
    (Classical.choose_spec (hex τ hτ)) (B.inducingMap (T.leviHalfCharacter B) a)
    (B.inducingMap (T.leviHalfCharacter B) (contragredientMap a)) (fun _ _ => rfl) ℓ

/-- The actual refined Levi has arbitrarily small compact open subgroups. -/
theorem refinedLevi_compactOpenCofinal {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B) :
    letI := T.topology
    ∀ H : OpenSubgroup (refinedLevi F.Carrier B S), ∃ L : OpenSubgroup (refinedLevi F.Carrier B S),
      IsCompact (L : Set (refinedLevi F.Carrier B S)) ∧ L ≤ H := by
  let := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  let := T.leviTopologicalGroup (B.flatten S)
  have := T.leviNonarchimedean (B.flatten S)
  have := T.leviLocallyCompactSpace (B.flatten S)
  let e := flattenedLeviEquivContinuous F.Carrier B S
  have : NonarchimedeanGroup (refinedLevi F.Carrier B S) :=
    NonarchimedeanGroup.nonarchimedean_of_emb e.toMulEquiv.toMonoidHom
      e.toHomeomorph.isOpenEmbedding
  have : LocallyCompactSpace (refinedLevi F.Carrier B S) :=
    e.toHomeomorph.locallyCompactSpace_iff.mp inferInstance
  intro H
  obtain ⟨L, hL, hLH⟩ := compactOpenSubgroupBasis (refinedLevi F.Carrier B S)
    (H : Set (refinedLevi F.Carrier B S)) H.mem_nhds_one
  exact ⟨L, hL, fun x hx => hLH hx⟩

/-- On a refined parabolic element supported in one block, the refined modulus
is the modulus of that block. -/
theorem refinedLeviModulus_mulSingle {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (j : Fin B.length) (q : (S j).parabolic F.Carrier)
    (q' : refinedParabolic F.Carrier B S)
    (hq' : (q' : B.Levi F.Carrier) = Pi.mulSingle j (q : GeneralLinear (B.size j) F.Carrier)) :
    (T.refinedLeviModulus B S (refinedLeviProjection F.Carrier B S q') : ℝ≥0) =
      (T.leviModulus (S j) ((S j).leviProjection F.Carrier q) : ℝ≥0) := by
  rw [T.refinedLeviModulus_apply, Units.coe_prod]
  simp only [PadicField.TopologicalData.refinedLeviBlock_projection]
  rw [Finset.prod_eq_single j]
  · have hj : refinedParabolicEval F.Carrier B S j q' = q := by
      apply Subtype.ext
      change (q' : B.Levi F.Carrier) j = q
      rw [hq', Pi.mulSingle_eq_same]
    rw [hj]
  · intro i _ hij
    have hi : refinedParabolicEval F.Carrier B S i q' = 1 := by
      apply Subtype.ext
      change (q' : B.Levi F.Carrier) i = 1
      rw [hq', Pi.mulSingle_eq_of_ne hij]
    rw [hi, map_one, map_one, Units.val_one]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The refined clause of natural induction duality follows from the scalar
compact integral for standard GL parabolics. -/
theorem refinedNaturalInductionDuality_of_scalar
    (hGL : GLParabolicCompactScalarIntegralStatement.{uF}) :
    RefinedNaturalInductionDualityClause.{uF, uV} := by
  intro p _ F T
  let := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  intro n B S
  let := T.leviTopologicalGroup B
  have := T.leviNonarchimedean B
  have := T.leviLocallyCompactSpace B
  have hdata := fun i => exists_compactScalarData T hGL (S i)
  choose Ki hKc hKμ using hdata
  let : ∀ i, MeasurableSpace (Ki i) := fun i => borel _
  have : ∀ i, BorelSpace (Ki i) := fun i => ⟨rfl⟩
  have : ∀ i, SecondCountableTopology (Ki i) := fun i => by
    have : SecondCountableTopology (GeneralLinear (B.size i) F.Carrier) :=
      T.generalLinearSecondCountableTopology (B.size i)
    exact TopologicalSpace.Subtype.secondCountableTopology
      (Ki i : Set (GeneralLinear (B.size i) F.Carrier))
  choose μi hprob hpos hscalar using hKμ
  let : MeasurableSpace (Subgroup.pi Set.univ Ki) := borel _
  have : BorelSpace (Subgroup.pi Set.univ Ki) := ⟨rfl⟩
  have := Induction.piSubgroupMeasure_isOpenPosMeasure Ki μi
  let δ : refinedParabolic F.Carrier B S → ℝ≥0 := fun q =>
    (T.refinedLeviModulus B S (refinedLeviProjection F.Carrier B S q) : ℝ≥0)
  have hscalarK := Induction.piSubgroup_scalarIntegral (fun i => (S i).parabolic F.Carrier) Ki μi
    (fun i q => (T.leviModulus (S i) ((S i).leviProjection F.Carrier q) : ℝ≥0))
    (fun i φ hφ hcov g => (hscalar i φ hφ hcov g).2) δ
    (fun j q q' hq' => refinedLeviModulus_mulSingle T B S j q q' hq')
  have hm : Continuous (refinedLeviProjection F.Carrier B S) :=
    (refinedLeviProjectionContinuous F.Carrier B S).continuous
  have hδ : ∀ q : refinedParabolic F.Carrier B S,
      (T.refinedParabolicHalfModulus B S q : ℂ) * T.refinedParabolicHalfModulus B S q =
        ((δ q : ℝ) : ℂ) := by
    intro q
    have h := congrArg Units.val
      (T.refinedLeviHalfModulus_sq B S (refinedLeviProjection F.Carrier B S q))
    rw [Units.val_pow_eq_pow_val, Jacquet.complexCharacter_apply, sq] at h
    exact h
  have hex := fun (σ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)) (hσ : IsAdmissible σ.ρ) =>
    Induction.exists_integralDualEquiv (refinedParabolic F.Carrier B S)
      (refinedLeviProjection F.Carrier B S) (T.refinedParabolicHalfModulus B S) δ
      (Subgroup.pi Set.univ Ki) (Induction.piSubgroupMeasure Ki μi) hm
      (T.isOpen_ker_refinedParabolicHalfModulus B S) hδ (refinedLevi_compactOpenCofinal T B S)
      hscalarK σ.ρ hσ.1 (normalizedRefinedInductionAdmissibility F T B S σ.ρ hσ)
  refine ⟨fun σ hσ => Classical.choose (hex σ hσ), ?_⟩
  intro σ τ hσ hτ a ℓ
  exact Induction.integralDualEquiv_natural (refinedParabolic F.Carrier B S)
    (refinedLeviProjection F.Carrier B S) (T.refinedParabolicHalfModulus B S)
    (Subgroup.pi Set.univ Ki) (Induction.piSubgroupMeasure Ki μi) σ.ρ τ.ρ _ _
    (Classical.choose_spec (hex σ hσ)) (Classical.choose_spec (hex τ hτ))
    (refinedInducingMap B S (T.refinedLeviHalfModulus B S) a)
    (refinedInducingMap B S (T.refinedLeviHalfModulus B S) (contragredientMap a))
    (fun _ _ => rfl) ℓ

/-- Natural normalized induction duality, standard and refined, follows from
the scalar compact integral for standard GL parabolics. -/
theorem naturalNormalizedInductionDuality_of_scalar
    (hGL : GLParabolicCompactScalarIntegralStatement.{uF}) :
    NaturalNormalizedInductionDualityStatement.{uF, uV} :=
  ⟨standardNaturalInductionDuality_of_scalar hGL, refinedNaturalInductionDuality_of_scalar hGL⟩

end Langlands.Parabolic
