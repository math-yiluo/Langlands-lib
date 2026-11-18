import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactComparison

/-! # Intrinsic cuspidality and conjugation bounds under compact change

The actual Xi comparison identifies the Schwartz spaces as subspaces of
the same functions. Intrinsic cuspidality, conjugation convergence and
the exact full-chamber bound then transfer without changing any function.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {Ξ Ξ' σ σ' : Γ → ℝ}

/-- A Schwartz-submodule equality as a linear equivalence preserving
the underlying function. -/
def Space.equivOfSubmoduleEq
    (h : schwartzSubmodule Ξ σ = schwartzSubmodule Ξ' σ') :
    Space Ξ σ ≃ₗ[ℂ] Space Ξ' σ' :=
  LinearEquiv.ofEq _ _ h

@[simp] theorem Space.coe_equivOfSubmoduleEq
    (h : schwartzSubmodule Ξ σ = schwartzSubmodule Ξ' σ') (f : Space Ξ σ) :
    (Space.equivOfSubmoduleEq h f : Γ → ℂ) = f :=
  LinearEquiv.coe_ofEq_apply h f

@[simp] theorem Space.coe_equivOfSubmoduleEq_symm
    (h : schwartzSubmodule Ξ σ = schwartzSubmodule Ξ' σ') (f : Space Ξ' σ') :
    ((Space.equivOfSubmoduleEq h).symm f : Γ → ℂ) = f :=
  LinearEquiv.coe_ofEq_apply h.symm f

end Generic

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K K' : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  (hK'c : IsCompact (K' : Set (rationalPoints G)))
  (hPK' : IsIwasawaPair (standardParabolicPoints i ν ∅) K'.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The actual Schwartz-space equivalence changing only the compact open
Iwasawa subgroup; its underlying function is unchanged. -/
def rationalSchwartzCompactEquiv :
    RationalSchwartzSpace hKc hPK ρ ≃ₗ[ℂ] RationalSchwartzSpace hK'c hPK' ρ :=
  Space.equivOfSubmoduleEq
    (rationalSchwartzSubmodule_eq K.isOpen hKc hPK K'.isOpen hK'c hPK' ρ)

@[simp] theorem coe_rationalSchwartzCompactEquiv
    (f : RationalSchwartzSpace hKc hPK ρ) :
    (rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ f : rationalPoints G → ℂ) = f :=
  Space.coe_equivOfSubmoduleEq _ f

@[simp] theorem coe_rationalSchwartzCompactEquiv_symm
    (f : RationalSchwartzSpace hK'c hPK' ρ) :
    ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f :
      rationalPoints G → ℂ) = f :=
  Space.coe_equivOfSubmoduleEq_symm _ f

/-- Intrinsic cuspidality is independent of the Xi-defining compact
because all its defining integrands are the same functions. -/
theorem rationalSchwartzCompactEquiv_mem_cuspidal_iff
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ f ∈
        rationalCuspidalSubmodule hK'c hPK' ρ ↔
      f ∈ rationalCuspidalSubmodule hKc hPK ρ := by
  simp only [mem_rationalCuspidalSubmodule, coe_rationalSchwartzCompactEquiv]

/-- The conjugation pairing keeps the exact complex value under the
compact comparison, without any convergence assumption. -/
theorem rationalConjugationPairing_compactEquiv
    (muG : Measure (rationalPoints G)) (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    (h : rationalPoints G) :
    rationalConjugationPairing hK'c hPK' ρ muG
        (rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ f₁)
        (rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ f₂) h =
      rationalConjugationPairing hKc hPK ρ muG f₁ f₂ h := by
  unfold rationalConjugationPairing
  rw [coe_rationalSchwartzCompactEquiv, coe_rationalSchwartzCompactEquiv]

/-- All-conjugators convergence transfers between the actual compact
choices, retaining the intrinsic cuspidal first argument. -/
theorem rationalCuspidalConjugationConverges_of_compact
    (muG : Measure (rationalPoints G))
    (hc : RationalCuspidalConjugationConverges hKc hPK ρ muG) :
    RationalCuspidalConjugationConverges hK'c hPK' ρ muG := by
  let e := rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ
  intro f₁ hf₁ f₂ h
  have hfc : e.symm f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ := by
    rw [mem_rationalCuspidalSubmodule]
    change ∀ I hI muU hmuU, IsIntegrableUnipotentCuspidal muU
      ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f₁ : rationalPoints G → ℂ)
    rw [coe_rationalSchwartzCompactEquiv_symm]
    exact hf₁
  have hh := hc (e.symm f₁) hfc (e.symm f₂) h
  change Integrable (conjugationIntegrand
    ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f₁ : rationalPoints G → ℂ)
    ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f₂ : rationalPoints G → ℂ) h) muG at hh
  rw [coe_rationalSchwartzCompactEquiv_symm, coe_rationalSchwartzCompactEquiv_symm] at hh
  exact hh

/-- The entire exact local VIII.3.1 conclusion transfers to any other
compact open Iwasawa choice, with the same full chamber, modulus and
matrix height. -/
theorem rationalCuspidalConjugationBound_of_compact
    (muG : Measure (rationalPoints G))
    (hc : RationalCuspidalConjugationBound hKc hPK ρ muG) :
    RationalCuspidalConjugationBound hK'c hPK' ρ muG := by
  let e := rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ
  refine ⟨rationalCuspidalConjugationConverges_of_compact hKc hPK hK'c hPK' ρ muG hc.1,
    fun f₁ hf₁ f₂ r => ?_⟩
  have hfc : e.symm f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ := by
    rw [mem_rationalCuspidalSubmodule]
    change ∀ I hI muU hmuU, IsIntegrableUnipotentCuspidal muU
      ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f₁ : rationalPoints G → ℂ)
    rw [coe_rationalSchwartzCompactEquiv_symm]
    exact hf₁
  obtain ⟨c, hpos, hbound⟩ := hc.2 (e.symm f₁) hfc (e.symm f₂) r
  refine ⟨c, hpos, fun a => ?_⟩
  have hba := hbound a
  unfold rationalConjugationPairing at hba ⊢
  change ‖conjugationPairing muG
    ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f₁ : rationalPoints G → ℂ)
    ((rationalSchwartzCompactEquiv hKc hPK hK'c hPK' ρ).symm f₂ : rationalPoints G → ℂ) a‖ ≤ _ at hba
  rw [coe_rationalSchwartzCompactEquiv_symm, coe_rationalSchwartzCompactEquiv_symm] at hba
  exact hba

/-- The exact local conjugation bound is independent of the compact
open Iwasawa subgroup defining the Schwartz space. -/
theorem rationalCuspidalConjugationBound_iff_compact
    (muG : Measure (rationalPoints G)) :
    RationalCuspidalConjugationBound hKc hPK ρ muG ↔
      RationalCuspidalConjugationBound hK'c hPK' ρ muG :=
  ⟨rationalCuspidalConjugationBound_of_compact hKc hPK hK'c hPK' ρ muG,
    rationalCuspidalConjugationBound_of_compact hK'c hPK' hKc hPK ρ muG⟩

end Langlands.HarishChandraSchwartz
