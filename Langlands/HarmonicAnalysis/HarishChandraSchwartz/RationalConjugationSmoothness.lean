import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalIntegrability
import Langlands.Topology.LocallyConstant.QuotientDescent

/-! # Smoothness of conjugation pairings on the actual split-central quotient

Bi-invariance makes the conjugate-function map locally constant. Its image on a
compact set is finite, and the totalized pairing descends as a locally constant
complex function. These facts require no convergence or Haar invariance.
-/

noncomputable section

universe u

open MeasureTheory Langlands.QuotientIntegration
open scoped Topology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {H : OpenSubgroup Γ} {f : Γ → ℂ}

/-- Bi-invariance under an open subgroup makes the entire conjugate function
locally constant as the conjugator varies. -/
theorem IsBiInvariant.isLocallyConstant_conjFun
    (hf : IsBiInvariant H.toSubgroup f) :
    IsLocallyConstant (fun h : Γ => conjFun h f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen {y : Γ | y * x⁻¹ ∈ H} :=
    H.isOpen.preimage (continuous_id.mul continuous_const)
  have hx : x ∈ {y : Γ | y * x⁻¹ ∈ H} := by
    change x * x⁻¹ ∈ H.toSubgroup
    simpa only [mul_inv_cancel] using H.toSubgroup.one_mem
  filter_upwards [hopen.mem_nhds hx] with y hy
  funext g
  have he : y * g * y⁻¹ =
      (y * x⁻¹) * (x * g * x⁻¹) * (y * x⁻¹)⁻¹ := by group
  change f (y * g * y⁻¹) = f (x * g * x⁻¹)
  rw [he]
  exact hf (y * x⁻¹) hy (y * x⁻¹)⁻¹ (H.inv_mem hy) (x * g * x⁻¹)

/-- The compact-conjugator finiteness used in Waldspurger VIII.3.2. -/
theorem IsBiInvariant.finite_conjFun_image
    (hf : IsBiInvariant H.toSubgroup f) {C : Set Γ} (hC : IsCompact C) :
    ((fun h : Γ => conjFun h f) '' C).Finite := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hlc := hf.isLocallyConstant_conjFun.comp_continuous
    (continuous_subtype_val : Continuous (Subtype.val : C → Γ))
  simpa only [Set.range_comp, Subtype.range_val] using hlc.range_finite

/-- The inverse-conjugator version for the second function in VIII.3.2. -/
theorem IsBiInvariant.finite_conjFun_inv_image
    (hf : IsBiInvariant H.toSubgroup f) {C : Set Γ} (hC : IsCompact C) :
    ((fun h : Γ => conjFun h⁻¹ f) '' C).Finite := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hlc := hf.isLocallyConstant_conjFun.comp_continuous
    (continuous_subtype_val.inv : Continuous (fun h : C => (h : Γ)⁻¹))
  apply hlc.range_finite.subset
  rintro φ ⟨h, hm, rfl⟩
  exact ⟨⟨h, hm⟩, rfl⟩

variable [MeasurableSpace Γ]

/-- Local constancy of the totalized integral follows without interchanging
limits or assuming inner convergence. -/
theorem IsBiInvariant.isLocallyConstant_conjugationPairing
    (hf : IsBiInvariant H.toSubgroup f) (μ : Measure Γ) (f₂ : Γ → ℂ) :
    IsLocallyConstant (conjugationPairing μ f f₂) := by
  change IsLocallyConstant (fun h : Γ => ∫ g, f (h * g * h⁻¹) * f₂ g ∂μ)
  exact hf.isLocallyConstant_conjFun.comp (fun φ : Γ → ℂ => ∫ g, φ g * f₂ g ∂μ)

/-- Pointwise central descent preserves local constancy in the genuine
left-quotient topology. -/
theorem IsBiInvariant.isLocallyConstant_leftConjugationPairing
    (hf : IsBiInvariant H.toSubgroup f)
    (A : Subgroup Γ) (hA : A ≤ Subgroup.center Γ) (μ : Measure Γ) (f₂ : Γ → ℂ) :
    IsLocallyConstant (leftConjugationPairing A hA μ f f₂) := by
  apply (Langlands.LocallyConstantQuotient.isLocallyConstant_iff
    (leftQuotientMap A) (leftQuotient_isOpenQuotientMap A).isQuotientMap _).mpr
  exact hf.isLocallyConstant_conjugationPairing μ f₂

end Generic

section Schwartz

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Nonempty (CompactOpenSubgroup Γ)] {Ξ σ : Γ → ℝ}

/-- The conjugate-function map of an actual Schwartz function as a locally
constant function, using one of its compact open levels. -/
def Space.locallyConstantConjugates (f : Space Ξ σ) : LocallyConstant Γ (Γ → ℂ) where
  toFun h := conjFun h (f : Γ → ℂ)
  isLocallyConstant := by
    obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
    exact IsBiInvariant.isLocallyConstant_conjFun (H := H.1) hH.1

theorem Space.finite_conjFun_image (f : Space Ξ σ) {C : Set Γ} (hC : IsCompact C) :
    ((fun h : Γ => conjFun h (f : Γ → ℂ)) '' C).Finite := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  exact IsBiInvariant.finite_conjFun_image (H := H.1) hH.1 hC

theorem Space.finite_conjFun_inv_image (f : Space Ξ σ) {C : Set Γ} (hC : IsCompact C) :
    ((fun h : Γ => conjFun h⁻¹ (f : Γ → ℂ)) '' C).Finite := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  exact IsBiInvariant.finite_conjFun_inv_image (H := H.1) hH.1 hC

variable [MeasurableSpace Γ]

/-- The descended totalized pairing of a Schwartz function with any function. -/
def Space.leftConjugationPairingLocallyConstant (f : Space Ξ σ)
    (A : Subgroup Γ) (hA : A ≤ Subgroup.center Γ) (μ : Measure Γ) (f₂ : Γ → ℂ) :
    LocallyConstant (LeftQuotient A) ℂ where
  toFun := leftConjugationPairing A hA μ (f : Γ → ℂ) f₂
  isLocallyConstant := by
    obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
    exact IsBiInvariant.isLocallyConstant_leftConjugationPairing
      (H := H.1) hH.1 A hA μ f₂

end Schwartz

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

include hKc in
theorem finite_rationalConjugates (f : RationalSchwartzSpace hKc hPK ρ)
    {C : Set (rationalPoints G)} (hC : IsCompact C) :
    ((fun h => conjFun h (f : rationalPoints G → ℂ)) '' C).Finite := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact f.finite_conjFun_image hC

include hKc in
theorem finite_rationalInverseConjugates (f : RationalSchwartzSpace hKc hPK ρ)
    {C : Set (rationalPoints G)} (hC : IsCompact C) :
    ((fun h => conjFun h⁻¹ (f : rationalPoints G → ℂ)) '' C).Finite := by
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact f.finite_conjFun_inv_image hC

/-- The exact actual split-central pairing with its proved local constancy. -/
def rationalLeftConjugationPairingLocallyConstant
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ) :
    LocallyConstant (LeftQuotient (rationalPoints.map s).range) ℂ := by
  letI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  exact f₁.leftConjugationPairingLocallyConstant (rationalPoints.map s).range
    hs.isCentralSplitTorus.isCentral.range_le_center muG (f₂ : rationalPoints G → ℂ)

@[simp] theorem rationalLeftConjugationPairingLocallyConstant_apply
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (q : LeftQuotient (rationalPoints.map s).range) :
    rationalLeftConjugationPairingLocallyConstant hKc hPK ρ s hs muG f₁ f₂ q =
      rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂ q := rfl

variable (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
  [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (rationalPoints.map s).range)]

/-- Bochner measurability on precisely the displayed Borel quotient in VIII.3.2. -/
theorem stronglyMeasurable_rationalLeftConjugationPairing
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ) :
    StronglyMeasurable (rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂) :=
  (rationalLeftConjugationPairingLocallyConstant hKc hPK ρ s hs muG f₁ f₂).continuous.stronglyMeasurable

/-- The adapter's a.e. strong measurability input holds for any measure on the
displayed Borel quotient, in particular for the target's compatible measure. -/
theorem aestronglyMeasurable_rationalLeftConjugationPairing
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)) :
    AEStronglyMeasurable (rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂) muQ :=
  (stronglyMeasurable_rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂).aestronglyMeasurable

end Rational

end Langlands.HarishChandraSchwartz
