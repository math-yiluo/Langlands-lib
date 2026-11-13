import Langlands.LocalFactor.SpectralConductorRankOneStatement
import Langlands.LocalFactor.DeligneHenniartIntermediateGeometricProof
import Langlands.LocalFactor.DeligneHenniartDimensionOneRelative
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteProof
import Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof
import Langlands.LocalFactor.Ramification.RankOneArtinSum

/-!
# Rank-one conductor transport at intermediate fields of the common closure: proof

Proof of `SpectralConductor.CommonClosureRankOneConductorStatement F` for every prime `p`
and p-adic field `F`. For real `s ≥ 0`:

1. `conductor_le_iff`: the conductor of the transported field character `χ̃` is at most
   `⌈s⌉` exactly when `χ` is trivial on the carried upper group
   `intermediateUpperGroup F L s` (upper-numbering reciprocity at `L`);
2. `upper_trivial_iff`: `χ` is trivial on that group exactly when `ρ` is trivial on the
   inertia elements of the upper group `G^s(M/L)` (restriction from the closure to `M`).

`Ramification.Padic.inertiaArtinConductor_rankOne_eq_of_upper_levels` then identifies the
Artin expression of `ρ` with `a(χ̃)`.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.LocalFactor.SpectralConductor.RankOneProof

open Ramification.Padic CommonClosure CommonClosureSpectralAnalytic Weil.Local LocalClassField
open VirtualRepresentation.LocalWeil.Ramification
open NonabelianSystem.DeligneHenniart

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Step 1: unit levels of the transported character are the carried upper groups. -/
theorem conductor_le_iff (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (L : Extension F) (χ : weilSubgroup F L →ₜ* ℂˣ) {s : ℝ} (hs : 0 ≤ s) :
    (fieldData F L).multiplicativeConductor (fieldCharacterEquiv F e L χ) ≤ ⌈s⌉₊ ↔
      ∀ g ∈ intermediateUpperGroup F L s, χ g = 1 := by
  have hW := intermediateUpperGroup_map_reciprocityUnits F
    (absoluteUpperReciprocityTheorems.{uF}.2.2.1) unitFiltrationComparison e L
    (Ramification.HerbrandBridge.absoluteUpperInertia _ _)
    (intermediateGeometricProof p F e he L) hs
  rw [← PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le]
  have h := trivial_iff_of_map_reciprocityUnits F (e := e) L (fieldCharacterEquiv F e L χ) _ _ hW
  rw [weilCharacter_fieldCharacterEquiv] at h
  exact h


/-! ## Step 2: the finite field `M` seen over `L` -/

section Restriction

open Ramification.HerbrandBridge

attribute [local instance] Ramification.HerbrandBridge.asPadicField_isScalarTower

variable (L : Extension F)
  (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
  (hLM : L.field ≤ M.toIntermediateField)

/-- `M` as a finite Galois extension of `L` inside the closure (same carrier). -/
abbrev overL : FiniteGaloisIntermediateField (L.asPadicField (p := p)).Carrier
    (AlgebraicClosure F.Carrier) :=
  extendFiniteGalois (F := F) (K := L.asPadicField (p := p)) (M := M) (fun x => hLM x.2)

/-- The identity of carriers between `M` over `L` and the statement's `L`-algebra `M`. -/
def overLEquiv :
    letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
      (IntermediateField.inclusion hLM).toAlgebra
    (finiteGaloisPadicField (L.asPadicField (p := p)) (overL F L M hLM)).Carrier ≃ₐ[L.field]
      (absoluteFiniteExtension F M).Carrier :=
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  { toFun x := ⟨x, x.2⟩
    invFun x := ⟨x, x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl
    commutes' _ := rfl }

/-- Restriction of an automorphism of the closure over `L` to `M`. -/
def restrictToM :
    letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
      (IntermediateField.inclusion hLM).toAlgebra
    (AlgebraicClosure F.Carrier ≃ₐ[L.field] AlgebraicClosure F.Carrier) →
      ((absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier) :=
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  fun τ => (overLEquiv F L M hLM).autCongr
    (AlgEquiv.restrictNormalHom (F := (L.asPadicField (p := p)).Carrier)
      (K₁ := AlgebraicClosure F.Carrier) (overL F L M hLM) τ)

theorem restrictToM_apply
    (τ : AlgebraicClosure F.Carrier ≃ₐ[L.field] AlgebraicClosure F.Carrier)
    (y : (absoluteFiniteExtension F M).Carrier) :
    letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
      (IntermediateField.inclusion hLM).toAlgebra
    ((restrictToM F L M hLM τ y : (absoluteFiniteExtension F M).Carrier) :
      AlgebraicClosure F.Carrier) = τ (y : AlgebraicClosure F.Carrier) := by
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  change ((AlgEquiv.restrictNormalHom (F := (L.asPadicField (p := p)).Carrier)
      (K₁ := AlgebraicClosure F.Carrier) (overL F L M hLM) τ ⟨y, y.2⟩ :
        (overL F L M hLM)) : AlgebraicClosure F.Carrier) = _
  rw [AlgEquiv.restrictNormalHom_apply]

/-- Restriction to `M` carries the upper filtration of the closure over `L` into the upper
filtration of `M/L`. -/
theorem restrictToM_mem_upper {s : ℝ}
    (τ : AlgebraicClosure F.Carrier ≃ₐ[L.field] AlgebraicClosure F.Carrier)
    (hτ : τ ∈ upperGroupIn (L.asPadicField (p := p)) (AlgebraicClosure F.Carrier) s) :
    letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
    letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
      (IntermediateField.inclusion hLM).toAlgebra
    letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    restrictToM F L M hLM τ ∈
      upperRamificationGroup (absoluteFiniteExtension F M).canonicalTopologicalData L.field s := by
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h := (mem_upperGroupIn_iff _ _ s τ).mp hτ (overL F L M hLM)
  exact (autCongr_mem_upperRamificationGroup_iff
    (finiteGaloisPadicField (L.asPadicField (p := p)) (overL F L M hLM)).canonicalTopologicalData
    (absoluteFiniteExtension F M).canonicalTopologicalData L.field
    (overLEquiv F L M hLM) s _).mpr h

/-- Every element of the upper group of `M/L` of index `s ≥ -1` is the restriction of an
element of the absolute upper group of `L`, carried to the closure of `F` by the literal
inclusion. -/
theorem exists_restrictToM_eq {s : ℝ} (hs : -1 ≤ s)
    (σ : letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
        (IntermediateField.inclusion hLM).toAlgebra
      (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field] (absoluteFiniteExtension F M).Carrier)
    (hσ : letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
      letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
        (IntermediateField.inclusion hLM).toAlgebra
      letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
        IsScalarTower.of_algebraMap_eq' rfl
      σ ∈ upperRamificationGroup (absoluteFiniteExtension F M).canonicalTopologicalData
        L.field s) :
    ∃ τ ∈ absoluteUpperRamificationGroup (L.asPadicField (p := p)) s,
      restrictToM F L M hLM ((intermediateClosureEquiv F L).autCongr τ) = σ := by
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨σ₁, rfl⟩ := (overLEquiv F L M hLM).autCongr.surjective σ
  have h₁ := (autCongr_mem_upperRamificationGroup_iff
    (finiteGaloisPadicField (L.asPadicField (p := p)) (overL F L M hLM)).canonicalTopologicalData
    (absoluteFiniteExtension F M).canonicalTopologicalData L.field
    (overLEquiv F L M hLM) s σ₁).mp hσ
  obtain ⟨σ₂, rfl⟩ := (comapFiniteGaloisEquiv (L.asPadicField (p := p))
    (intermediateClosureEquiv F L) (overL F L M hLM)).autCongr.surjective σ₁
  have h₂ := (autCongr_mem_upperRamificationGroup_iff
    (finiteGaloisPadicField (L.asPadicField (p := p)) (comapFiniteGalois
      (L.asPadicField (p := p)) (intermediateClosureEquiv F L)
        (overL F L M hLM))).canonicalTopologicalData
    (finiteGaloisPadicField (L.asPadicField (p := p)) (overL F L M hLM)).canonicalTopologicalData
    (L.asPadicField (p := p)).Carrier
    (comapFiniteGaloisEquiv (L.asPadicField (p := p))
      (intermediateClosureEquiv F L) (overL F L M hLM)) s σ₂).mp h₁
  have h₃ : σ₂ ∈ (absoluteUpperRamificationGroup (L.asPadicField (p := p)) s).map
      (absoluteFiniteRestriction (L.asPadicField (p := p)) (comapFiniteGalois
        (L.asPadicField (p := p)) (intermediateClosureEquiv F L)
          (overL F L M hLM))).toMonoidHom := by
    rw [absoluteUpperFiniteImage (L.asPadicField (p := p)) _ s hs]
    exact h₂
  obtain ⟨τ, hτ, hτσ⟩ := h₃
  refine ⟨τ, hτ, ?_⟩
  have key := autCongr_restrictNormalHom (L.asPadicField (p := p))
    (intermediateClosureEquiv F L) (overL F L M hLM) τ
  change (overLEquiv F L M hLM).autCongr
    (AlgEquiv.restrictNormalHom (F := (L.asPadicField (p := p)).Carrier)
      (K₁ := AlgebraicClosure F.Carrier) (overL F L M hLM)
        ((intermediateClosureEquiv F L).autCongr τ)) = _
  rw [← key]
  exact congrArg _ (congrArg _ hτσ)

/-- Step 2: for `s ≥ 0`, `χ` kills the carried upper group of `W_L` of index `s` exactly when
`ρ` kills the upper group of `M/L` of index `s`. -/
theorem upper_trivial_iff (χ : weilSubgroup F L →ₜ* ℂˣ)
    (ρ : letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
      letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
        (IntermediateField.inclusion hLM).toAlgebra
      letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
        IsScalarTower.of_algebraMap_eq' rfl
      inertia (absoluteFiniteExtension F M).canonicalTopologicalData L.field →* ℂˣ)
    (hρ : letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
      letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
        (IntermediateField.inclusion hLM).toAlgebra
      letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
        IsScalarTower.of_algebraMap_eq' rfl
      ∀ (w : weilSubgroup F L), (w : localWeilGroup F) ∈ localInertia F →
        ∀ σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData L.field,
          (∀ y : (absoluteFiniteExtension F M).Carrier,
            ((σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field]
              (absoluteFiniteExtension F M).Carrier) y : AlgebraicClosure F.Carrier) =
              AlgEquiv.toAlgHom (localProjection F (w : localWeilGroup F))
                (y : AlgebraicClosure F.Carrier)) →
          ρ σ = χ w)
    {s : ℝ} (hs : 0 ≤ s) :
    letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
    letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
      (IntermediateField.inclusion hLM).toAlgebra
    letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
      IsScalarTower.of_algebraMap_eq' rfl
    (∀ g ∈ intermediateUpperGroup F L s, χ g = 1) ↔
      ∀ σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData L.field,
        (σ : (absoluteFiniteExtension F M).Carrier ≃ₐ[L.field]
          (absoluteFiniteExtension F M).Carrier) ∈
          upperRamificationGroup (absoluteFiniteExtension F M).canonicalTopologicalData
            L.field s → ρ σ = 1 := by
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hinert := Ramification.HerbrandBridge.absoluteUpperInertia (L.asPadicField (p := p))
    (L.asPadicField (p := p)).canonicalTopologicalData
  have act : ∀ (w : localWeilGroup (L.asPadicField (p := p)))
      (y : (absoluteFiniteExtension F M).Carrier),
      ((restrictToM F L M hLM ((intermediateClosureEquiv F L).autCongr
          (localProjection (L.asPadicField (p := p)) w)) y :
        (absoluteFiniteExtension F M).Carrier) : AlgebraicClosure F.Carrier) =
        AlgEquiv.toAlgHom (localProjection F (intermediateWeilEquiv F L w : localWeilGroup F))
          (y : AlgebraicClosure F.Carrier) := by
    intro w y
    rw [restrictToM_apply, intermediateWeilEquiv_projection, intermediateGaloisMap_apply]
    rfl
  constructor
  · intro hχ σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := exists_restrictToM_eq F L M hLM (by linarith) (σ : _) hσ
    have hτ0 : τ ∈ absoluteUpperRamificationGroup (L.asPadicField (p := p)) 0 :=
      absoluteUpperRamificationGroup_antitone (L.asPadicField (p := p)) hs hτ
    rw [hinert] at hτ0
    obtain ⟨w, hw⟩ := absoluteInertia_le_range_localProjection (L.asPadicField (p := p)) hτ0
    change localProjection (L.asPadicField (p := p)) w = τ at hw
    subst hw
    have hg : intermediateWeilEquiv F L w ∈ intermediateUpperGroup F L s := ⟨w, hτ, rfl⟩
    have hgI := intermediateUpperGroup_le_inertia F L hinert hs hg
    have h := hρ (intermediateWeilEquiv F L w) hgI σ (fun y => by rw [← hτσ]; exact act w y)
    rw [h]
    exact hχ _ hg
  · intro hρ1 g hg
    obtain ⟨w, hw, rfl⟩ := hg
    have hgI := intermediateUpperGroup_le_inertia F L hinert hs ⟨w, hw, rfl⟩
    have hτ := (mem_absoluteUpperRamificationGroup_iff_autCongr (L.asPadicField (p := p))
      (intermediateClosureEquiv F L) s _).mp hw
    have hσ := restrictToM_mem_upper F L M hLM _ hτ
    have hσI : restrictToM F L M hLM ((intermediateClosureEquiv F L).autCongr
        (localProjection (L.asPadicField (p := p)) w)) ∈
        inertia (absoluteFiniteExtension F M).canonicalTopologicalData L.field := by
      have h0 := upperRamificationGroup_antitone
        (absoluteFiniteExtension F M).canonicalTopologicalData L.field hs hσ
      rwa [upperRamificationGroup_zero] at h0
    have h := hρ _ hgI ⟨_, hσI⟩ (act w)
    rw [hρ1 ⟨_, hσI⟩ hσ] at h
    exact h.symm

end Restriction

end Langlands.LocalFactor.SpectralConductor.RankOneProof

namespace Langlands.LocalFactor.SpectralConductor

open RankOneProof Ramification.Padic CommonClosure CommonClosureSpectralAnalytic Weil.Local

universe uF

/-- **Rank-one conductor transport at intermediate fields of the common closure.** -/
theorem commonClosureRankOneConductor :
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      CommonClosureRankOneConductorStatement F := by
  intro p _ F e he L M hLM χ ρ hρ
  letI : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  letI : Algebra L.field (absoluteFiniteExtension F M).Carrier :=
    (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower (Padic p) L.field (absoluteFiniteExtension F M).Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact_mod_cast Ramification.Padic.inertiaArtinConductor_rankOne_eq_of_upper_levels _ _ ρ _
    (fun s hs => (conductor_le_iff F e he L χ hs).trans (upper_trivial_iff F L M hLM χ ρ hρ hs))

end Langlands.LocalFactor.SpectralConductor
