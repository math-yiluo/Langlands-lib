import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviSchwartz
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrability
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Haar measures and integrals on the standard Levi scheme

Transport a chosen measure on the actual standard Levi subgroup through its canonical
rational-point equivalence. This preserves Haar measure, compact normalization, square-weight
integrability, the `L²` pairing and convolution.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section MeasurableTransport

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]

/-- Change of variables for the square-weight integral, with any real exponent. -/
theorem lintegral_squareWeight_map_equiv (e : X ≃ᵐ Y) (μX : Measure X)
    (Ξ σ : Y → ℝ) (d : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Ξ y ^ 2 * (1 + σ y) ^ (-d)) ∂(μX.map e)) =
      ∫⁻ x, ENNReal.ofReal (Ξ (e x) ^ 2 * (1 + σ (e x)) ^ (-d)) ∂μX :=
  lintegral_map_equiv _ e

/-- Square-weight integrability is unchanged by a measurable equivalence. -/
theorem squareIntegrableWeight_map_equiv_iff (e : X ≃ᵐ Y) (μX : Measure X)
    (Ξ σ : Y → ℝ) :
    SquareIntegrableWeight (μX.map e) Ξ σ ↔
      SquareIntegrableWeight μX (Ξ ∘ e) (σ ∘ e) := by
  simp only [SquareIntegrableWeight, lintegral_squareWeight_map_equiv, Function.comp_apply]

/-- All three `L²` weight hypotheses transport through a measurable equivalence. -/
theorem L2Weights.map_equiv_iff (e : X ≃ᵐ Y) (μX : Measure X) (Ξ σ : Y → ℝ) :
    L2Weights (μX.map e) Ξ σ ↔ L2Weights μX (Ξ ∘ e) (σ ∘ e) := by
  constructor
  · intro h
    refine ⟨fun x => h.pos (e x), fun x => h.nonneg (e x), ?_⟩
    simpa only [lintegral_squareWeight_map_equiv, Function.comp_apply] using h.square
  · intro h
    refine ⟨fun y => ?_, fun y => ?_, ?_⟩
    · simpa only [Function.comp_apply, e.apply_symm_apply] using h.pos (e.symm y)
    · simpa only [Function.comp_apply, e.apply_symm_apply] using h.nonneg (e.symm y)
    · simpa only [lintegral_squareWeight_map_equiv, Function.comp_apply] using h.square

/-- The integral defining the `L²` pairing obeys exact change of variables. -/
theorem pairing_map_equiv (e : X ≃ᵐ Y) (μX : Measure X) (f₁ f₂ : Y → ℂ) :
    pairing (μX.map e) f₁ f₂ = pairing μX (f₁ ∘ e) (f₂ ∘ e) := by
  exact integral_map_equiv e _

end MeasurableTransport

section GroupTransport

variable {H : Type u} {G : Type v} [Group H] [Group G]
  [TopologicalSpace H] [TopologicalSpace G]
  [MeasurableSpace H] [MeasurableSpace G] [BorelSpace H] [BorelSpace G]

/-- Convolution is compatible with a topological group equivalence and the mapped measure. -/
theorem convolution_map_continuousMulEquiv (e : H ≃ₜ* G) (μX : Measure H)
    (f₁ f₂ : G → ℂ) (h : H) :
    convolution (μX.map e) f₁ f₂ (e h) =
      convolution μX (f₁ ∘ e) (f₂ ∘ e) h := by
  change (∫ g, f₁ g * f₂ (g⁻¹ * e h) ∂(μX.map e.toHomeomorph.toMeasurableEquiv)) = _
  rw [integral_map_equiv]
  change (∫ x, f₁ (e x) * f₂ ((e x)⁻¹ * e h) ∂μX) = _
  simp only [convolution_apply, Function.comp_apply, map_mul, map_inv]

end GroupTransport

section Levi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance leviMeasureIsAffineHom (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance leviMeasureLocallyOfFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- A chosen measure on the actual Levi subgroup, read on its representing group scheme. -/
def leviSchemeMeasure (μM : Measure (standardLeviPoints i ν J)) :
    Measure (rationalPoints (Standard.leviScheme i ν J)) :=
  μM.map (leviSchemePointsEquiv i ν J).symm

variable {i ν J}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Mapping back to the actual subgroup recovers the chosen measure exactly. -/
@[simp] theorem map_leviSchemeMeasure (μM : Measure (standardLeviPoints i ν J)) :
    (leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J) = μM :=
  (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv.map_map_symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The point equivalence preserves the chosen subgroup measure. -/
theorem measurePreserving_leviSchemePointsEquiv (μM : Measure (standardLeviPoints i ν J)) :
    MeasurePreserving (leviSchemePointsEquiv i ν J) (leviSchemeMeasure i ν J μM) μM :=
  ⟨(leviSchemePointsEquiv i ν J).continuous.measurable, map_leviSchemeMeasure μM⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The inverse point equivalence also preserves the corresponding measures. -/
theorem measurePreserving_leviSchemePointsEquiv_symm
    (μM : Measure (standardLeviPoints i ν J)) :
    MeasurePreserving (leviSchemePointsEquiv i ν J).symm μM (leviSchemeMeasure i ν J μM) :=
  ⟨(leviSchemePointsEquiv i ν J).symm.continuous.measurable, rfl⟩

/-- The transported measure is Haar whenever the chosen subgroup measure is Haar. -/
instance leviSchemeMeasure_isHaarMeasure (μM : Measure (standardLeviPoints i ν J))
    [μM.IsHaarMeasure] : (leviSchemeMeasure i ν J μM).IsHaarMeasure :=
  (leviSchemePointsEquiv i ν J).symm.isHaarMeasure_map μM

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The volume of the inherited compact subgroup is preserved exactly. -/
theorem leviSchemeMeasure_compact (μM : Measure (standardLeviPoints i ν J))
    (K : Subgroup (rationalPoints G)) :
    leviSchemeMeasure i ν J μM (leviSchemeCompact K i ν J) =
      μM (K.subgroupOf (standardLeviPoints i ν J)) := by
  change (μM.map (leviSchemePointsEquiv i ν J).symm.toHomeomorph.toMeasurableEquiv)
    (leviSchemeCompact K i ν J) = _
  rw [(leviSchemePointsEquiv i ν J).symm.toHomeomorph.toMeasurableEquiv.map_apply]
  congr 1
  ext m
  change (leviSchemePointsEquiv i ν J).symm m ∈ leviSchemeCompact K i ν J ↔ _
  rw [mem_leviSchemeCompact_iff, ContinuousMulEquiv.apply_symm_apply]
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- In particular, Waldspurger's volume-one normalization is preserved. -/
theorem leviSchemeMeasure_compact_eq_one (μM : Measure (standardLeviPoints i ν J))
    {K : Subgroup (rationalPoints G)}
    (hμM : μM (K.subgroupOf (standardLeviPoints i ν J)) = 1) :
    leviSchemeMeasure i ν J μM (leviSchemeCompact K i ν J) = 1 := by
  rw [leviSchemeMeasure_compact, hμM]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Pairings of corresponding functions agree for the transported measure. -/
theorem pairing_leviSchemeMeasure (μM : Measure (standardLeviPoints i ν J))
    (f₁ f₂ : standardLeviPoints i ν J → ℂ) :
    pairing (leviSchemeMeasure i ν J μM)
        (f₁ ∘ leviSchemePointsEquiv i ν J) (f₂ ∘ leviSchemePointsEquiv i ν J) =
      pairing μM f₁ f₂ := by
  have h := pairing_map_equiv (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv
    (leviSchemeMeasure i ν J μM) f₁ f₂
  change pairing ((leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J))
    f₁ f₂ = _ at h
  rw [map_leviSchemeMeasure] at h
  exact h.symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Corresponding functions have exactly the same extended `Lᵖ` norm. -/
theorem eLpNorm_leviSchemeMeasure (μM : Measure (standardLeviPoints i ν J))
    (f : standardLeviPoints i ν J → ℂ) (p : ℝ≥0∞) :
    eLpNorm (f ∘ leviSchemePointsEquiv i ν J) p (leviSchemeMeasure i ν J μM) =
      eLpNorm f p μM := by
  let e := (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv
  have h := e.measurableEmbedding.eLpNorm_map_measure
    (g := f) (p := p) («μ» := leviSchemeMeasure i ν J μM)
  change eLpNorm f p ((leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J)) = _ at h
  rw [map_leviSchemeMeasure] at h
  exact h.symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- In particular, square integrability of corresponding functions is equivalent. -/
theorem memLp_leviSchemeMeasure_iff (μM : Measure (standardLeviPoints i ν J))
    (f : standardLeviPoints i ν J → ℂ) (p : ℝ≥0∞) :
    MemLp (f ∘ leviSchemePointsEquiv i ν J) p (leviSchemeMeasure i ν J μM) ↔
      MemLp f p μM := by
  let e := (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv
  have h := e.memLp_map_measure_iff (g := f) (p := p) («μ» := leviSchemeMeasure i ν J μM)
  change MemLp f p ((leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J)) ↔ _ at h
  rw [map_leviSchemeMeasure] at h
  exact h.symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Convolution of corresponding functions agrees pointwise. -/
theorem convolution_leviSchemeMeasure (μM : Measure (standardLeviPoints i ν J))
    (f₁ f₂ : standardLeviPoints i ν J → ℂ)
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    convolution (leviSchemeMeasure i ν J μM)
        (f₁ ∘ leviSchemePointsEquiv i ν J) (f₂ ∘ leviSchemePointsEquiv i ν J) x =
      convolution μM f₁ f₂ (leviSchemePointsEquiv i ν J x) := by
  have h := convolution_map_continuousMulEquiv (leviSchemePointsEquiv i ν J)
    (leviSchemeMeasure i ν J μM) f₁ f₂ x
  rw [map_leviSchemeMeasure] at h
  exact h.symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Absolute convergence of the convolution integral transfers in both directions. -/
theorem integrable_convolution_leviSchemeMeasure_iff
    (μM : Measure (standardLeviPoints i ν J)) (f₁ f₂ : standardLeviPoints i ν J → ℂ)
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    Integrable (fun y => f₁ (leviSchemePointsEquiv i ν J y) *
        f₂ (leviSchemePointsEquiv i ν J (y⁻¹ * x))) (leviSchemeMeasure i ν J μM) ↔
      Integrable (fun m => f₁ m * f₂ (m⁻¹ * leviSchemePointsEquiv i ν J x)) μM := by
  let e := (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv
  have h := integrable_map_equiv e
    (fun m => f₁ m * f₂ (m⁻¹ * leviSchemePointsEquiv i ν J x))
    («μ» := leviSchemeMeasure i ν J μM)
  change Integrable _ ((leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J)) ↔ _ at h
  rw [map_leviSchemeMeasure] at h
  change Integrable (fun m => f₁ m * f₂ (m⁻¹ * leviSchemePointsEquiv i ν J x)) μM ↔
    Integrable (fun y => f₁ (leviSchemePointsEquiv i ν J y) *
      f₂ ((leviSchemePointsEquiv i ν J y)⁻¹ * leviSchemePointsEquiv i ν J x))
      (leviSchemeMeasure i ν J μM) at h
  simpa only [map_mul, map_inv] using h.symm

section Weights

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

include hKo

/-- The square-weight integrals on the scheme and subgroup agree for every real exponent. -/
theorem lintegral_squareWeight_leviSchemeMeasure (μM : Measure (standardLeviPoints i ν J))
    (d : ℝ) :
    (∫⁻ x, ENNReal.ofReal
      (rationalXi (isCompact_leviSchemeCompact hKc)
          (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM) x ^ 2 *
        (1 + rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J)) x) ^ (-d))
      ∂(leviSchemeMeasure i ν J μM)) =
    ∫⁻ m, ENNReal.ofReal
      (rationalLeviXi hKc hM m ^ 2 * (1 + rationalHeight (F := F) ρ m) ^ (-d)) ∂μM := by
  have h := lintegral_squareWeight_map_equiv
    (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv
    (leviSchemeMeasure i ν J μM) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m) d
  change (∫⁻ m, ENNReal.ofReal
      (rationalLeviXi hKc hM m ^ 2 * (1 + rationalHeight (F := F) ρ m) ^ (-d))
      ∂((leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J))) = _ at h
  rw [map_leviSchemeMeasure] at h
  simp_rw [rationalXi_leviScheme hG hi hν hJ hKo hKc hM,
    rationalHeight_restrict_leviHom]
  exact h.symm

/-- The conclusion of II.1.5 for the scheme is equivalent to that for the actual subgroup. -/
theorem squareIntegrableWeight_leviSchemeMeasure_iff
    (μM : Measure (standardLeviPoints i ν J)) :
    SquareIntegrableWeight (leviSchemeMeasure i ν J μM)
      (rationalXi (isCompact_leviSchemeCompact hKc)
        (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM))
      (rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J))) ↔
    SquareIntegrableWeight μM (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m) := by
  simp only [SquareIntegrableWeight,
    lintegral_squareWeight_leviSchemeMeasure hG hi hν hJ hKo hKc ρ hM]

/-- The full `L²` weight hypotheses agree between the scheme and actual subgroup. -/
theorem l2Weights_leviSchemeMeasure_iff (μM : Measure (standardLeviPoints i ν J)) :
    L2Weights (leviSchemeMeasure i ν J μM)
      (rationalXi (isCompact_leviSchemeCompact hKc)
        (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM))
      (rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J))) ↔
    L2Weights μM (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m) := by
  have hΞ :
      rationalXi (isCompact_leviSchemeCompact hKc)
          (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM) =
        rationalLeviXi hKc hM ∘
          (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv :=
    funext (rationalXi_leviScheme hG hi hν hJ hKo hKc hM)
  have hσ :
      rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J)) =
        (fun m : standardLeviPoints i ν J => rationalHeight (F := F) ρ m) ∘
          (leviSchemePointsEquiv i ν J).toHomeomorph.toMeasurableEquiv :=
    funext (rationalHeight_restrict_leviHom ρ)
  rw [hΞ, hσ, ← L2Weights.map_equiv_iff]
  change L2Weights ((leviSchemeMeasure i ν J μM).map (leviSchemePointsEquiv i ν J))
    (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m) ↔ _
  rw [map_leviSchemeMeasure]

/-- The Schwartz equivalence preserves the `L²` pairing with the corresponding measures. -/
theorem pairing_rationalLeviSchwartzEquiv (μM : Measure (standardLeviPoints i ν J))
    (f₁ f₂ : Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m)) :
    pairing (leviSchemeMeasure i ν J μM)
        (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f₁)
        (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f₂) =
      pairing μM f₁ f₂ :=
  pairing_leviSchemeMeasure μM f₁ f₂

/-- The Schwartz equivalence preserves every `Lᵖ` norm, in particular the `L²` norm. -/
theorem eLpNorm_rationalLeviSchwartzEquiv (μM : Measure (standardLeviPoints i ν J))
    (f : Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m))
    (p : ℝ≥0∞) :
    eLpNorm (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f) p
        (leviSchemeMeasure i ν J μM) = eLpNorm (f : standardLeviPoints i ν J → ℂ) p μM :=
  eLpNorm_leviSchemeMeasure μM f p

/-- The convolution integrals of Schwartz functions correspond under the same equivalence. -/
theorem convolution_rationalLeviSchwartzEquiv (μM : Measure (standardLeviPoints i ν J))
    (f₁ f₂ : Space (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m))
    (x : rationalPoints (Standard.leviScheme i ν J)) :
    convolution (leviSchemeMeasure i ν J μM)
        (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f₁)
        (rationalLeviSchwartzEquiv hG hi hν hJ hKo hKc ρ hM f₂) x =
      convolution μM f₁ f₂ (leviSchemePointsEquiv i ν J x) :=
  convolution_leviSchemeMeasure μM f₁ f₂ x

end Weights

end Levi

end Langlands.HarishChandraSchwartz
