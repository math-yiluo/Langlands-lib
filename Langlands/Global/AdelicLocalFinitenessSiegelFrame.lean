import Langlands.Global.AdelicWeightedPointwiseConvolution
import Langlands.Global.AdelicStandardConstantTermIntegral
import Langlands.Global.EisensteinConstantTerm.Points

/-! # The weighted Siegel Hilbert space on the adelic group

The image of `P₀(F)` used by the weighted Siegel spaces (the principal image of the
represented minimal parabolic) is the image used by the standard constant terms. The quotient
map from `G(𝔸)`, with `W · Haar` on the fundamental domain for the chamber density `W`, is
measure preserving onto the weighted measure of the rational-parabolic quotient, and the
weighted automorphic Hilbert space embeds isometrically into `L²` on `G(𝔸)`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints Langlands.GroupScheme

section Comparison

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

private instance : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left

/-- The principal image of the represented minimal parabolic is the image of the rational points
of the standard minimal parabolic subgroup functor. -/
theorem parabolicPrincipalSubgroup_eq_minimalParabolicImage :
    parabolicPrincipalSubgroup F (Standard.parabolicHom i ν ∅) =
      StandardConstantTerm.minimalParabolicImage F G i ν := by
  have hrange := (Standard.isRepresentedBy_parabolicHom i ν ∅).2
  ext y
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    change map F _ G (Standard.parabolicHom i ν ∅) (rational F _ q) ∈ _
    rw [map_rational]
    apply StandardConstantTerm.mem_minimalParabolicImage_of_rational
    rw [← hrange]
    exact ⟨q, rfl⟩
  · rintro ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    rw [← hrange] at hx
    obtain ⟨q, hq⟩ := hx
    let q' : RationalGroupPoints F (Standard.parabolicScheme i ν ∅) := q
    refine ⟨rational F _ q', ⟨q', rfl⟩, ?_⟩
    change map F _ G (Standard.parabolicHom i ν ∅) (rational F _ q') = AdelicGroupPoints.rational F G x
    rw [map_rational]
    exact congrArg (AdelicGroupPoints.rational F G) hq

/-- Fundamental domains of equal discrete subgroups agree. -/
theorem fundamentalDomain_congr {Γ₁ Γ₂ : Subgroup (AdelicGroupPoints F G)} (h : Γ₁ = Γ₂)
    (h₁ : IsDiscrete (Γ₁ : Set (AdelicGroupPoints F G)))
    (h₂ : IsDiscrete (Γ₂ : Set (AdelicGroupPoints F G))) :
    LeftCosetSpace.fundamentalDomain Γ₁ h₁ = LeftCosetSpace.fundamentalDomain Γ₂ h₂ := by
  subst h
  rfl

end Comparison

section Frame

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G
local notation "D" => LeftCosetSpace.fundamentalDomain (parabolicPrincipalSubgroup F p)
  (isDiscrete_parabolicPrincipalSubgroup F p)

/-- `W · Haar` on the fundamental domain of the principal image of `P(F)`, for the chamber
density `W` of a log weight and a region of heights. -/
def frameMeasure (ell : RealCharacterDual F P → ℝ) (S : Set (RealCharacterDual F P)) : Measure A :=
  ((Measure.haar : Measure A).restrict D).withDensity (chamberDensity F p hK ell S)

/-- The quotient map pushes the frame measure to the weighted domain measure. -/
theorem map_mk_frameMeasure (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S : Set (RealCharacterDual F P)) (hS : @MeasurableSet _ (borel _) S) :
    Measure.map (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p)) (frameMeasure hK ell S) =
      domainMeasure F p hK ell (domainHeight F p hK ⁻¹' S) := by
  have hmk : Measurable (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p)) :=
    LeftCosetSpace.measurable_mk _
  have hW : Measurable (chamberDensity F p hK ell S) := by
    let : MeasurableSpace (RealCharacterDual F P) := borel _
    have : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
    exact (ENNReal.continuous_ofReal.comp ((continuous_const.mul
      (hell.comp hK.continuous_height)).rexp)).measurable.indicator
      (hK.continuous_height.measurable hS)
  ext s hs
  rw [Measure.map_apply hmk hs, frameMeasure, withDensity_apply _ (hmk hs),
    ← lintegral_indicator (hmk hs), ← lintegral_indicator_one hs,
    lintegral_domainMeasure_eq_chamberDensity F p hK ell hell S hS
      ((measurable_const.indicator hs) : Measurable (s.indicator 1))]
  refine lintegral_congr fun g => ?_
  by_cases hg : LeftCosetSpace.mk (parabolicPrincipalSubgroup F p) g ∈ s
  · have hg' : g ∈ LeftCosetSpace.mk (parabolicPrincipalSubgroup F p) ⁻¹' s := hg
    rw [indicator_of_mem hg', indicator_of_mem hg, Pi.one_apply, one_mul]
  · have hg' : g ∉ LeftCosetSpace.mk (parabolicPrincipalSubgroup F p) ⁻¹' s := hg
    rw [indicator_of_notMem hg', indicator_of_notMem hg, zero_mul]

/-- The quotient map from the frame measure to the weighted domain measure is measure
preserving. -/
theorem measurePreserving_mk_frameMeasure (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S : Set (RealCharacterDual F P)) (hS : @MeasurableSet _ (borel _) S) :
    MeasurePreserving (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p)) (frameMeasure hK ell S)
      (domainMeasure F p hK ell (domainHeight F p hK ⁻¹' S)) :=
  ⟨LeftCosetSpace.measurable_mk _, map_mk_frameMeasure hK ell hell S hS⟩

/-- The isometric embedding of the weighted automorphic Hilbert space of the domain
`H_P⁻¹(S)` into `L²` of the frame measure on `G(𝔸)`: composition with the quotient map
`G(𝔸) → G(F) \ G(𝔸)`. -/
def frameEmbedding (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S : Set (RealCharacterDual F P)) (hS : @MeasurableSet _ (borel _) S) :
    HilbertSpace F p hK ell (domainHeight F p hK ⁻¹' S) →ₗᵢ[ℂ] Lp ℂ 2 (frameMeasure hK ell S) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p))
    (measurePreserving_mk_frameMeasure hK ell hell S hS)).comp
      (pullback F p hK ell (domainHeight F p hK ⁻¹' S))

/-- The frame embedding is composition with the quotient map on representatives. -/
theorem frameEmbedding_ae (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S : Set (RealCharacterDual F P)) (hS : @MeasurableSet _ (borel _) S)
    (f : HilbertSpace F p hK ell (domainHeight F p hK ⁻¹' S)) :
    frameEmbedding hK ell hell S hS f =ᵐ[frameMeasure hK ell S]
      fun g => f (LeftCosetSpace.mk (rationalSubgroup F G) g) := by
  have h1 := Lp.coeFn_compMeasurePreserving (pullback F p hK ell (domainHeight F p hK ⁻¹' S) f)
    (measurePreserving_mk_frameMeasure hK ell hell S hS)
  have h2 := (measurePreserving_mk_frameMeasure hK ell hell S hS).quasiMeasurePreserving.ae_eq_comp
    (pullback_ae F p hK ell (domainHeight F p hK ⁻¹' S) f)
  exact h1.trans h2

end Frame

section StandardFrame

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

private instance : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left

/-- For the represented standard minimal parabolic, the frame measure is `W · Haar` on the
fundamental domain of the image of `P₀(F)` used by the standard constant terms. -/
theorem frameMeasure_eq_standard {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (ell : RealCharacterDual F (Standard.parabolicScheme i ν ∅) → ℝ)
    (S : Set (RealCharacterDual F (Standard.parabolicScheme i ν ∅))) :
    frameMeasure hK ell S =
      ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict
        (LeftCosetSpace.fundamentalDomain (StandardConstantTerm.minimalParabolicImage F G i ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G i ν))).withDensity
        (chamberDensity F (Standard.parabolicHom i ν ∅) hK ell S) := by
  rw [frameMeasure, fundamentalDomain_congr F (parabolicPrincipalSubgroup_eq_minimalParabolicImage F i ν)]

end StandardFrame

end Langlands.Global.WeightedSiegel
