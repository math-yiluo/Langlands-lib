import Langlands.Representation.Aubert.General.FirstAdjointness
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryProof
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Multiplicity one in the actual Jacquet Hom space detects irreducible induction -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

open _root_.CategoryTheory SmoothRep

section Scalar

variable {H : Type uG} [Group H] [TopologicalSpace H]
  (π : SmoothRep.{0, uG, uV} ℂ H) [Nontrivial π]

/-- A one-dimensional intertwining space is spanned by the identity endomorphism. -/
theorem exists_scalar_of_rank_endomorphism_le_one
    (hdim : Module.rank ℂ (π.representation.IntertwiningMap π.representation) ≤ 1)
    (f : π.representation.IntertwiningMap π.representation) :
    ∃ c : ℂ, c • Representation.IntertwiningMap.id π.representation = f := by
  obtain ⟨v, hv⟩ := (rank_le_one_iff (K := ℂ)
    (V := π.representation.IntertwiningMap π.representation)).mp hdim
  obtain ⟨a, ha⟩ := hv (Representation.IntertwiningMap.id π.representation)
  have ha0 : a ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have he := congrArg (fun F => F x) ha
    rw [h, zero_smul] at he
    exact hx he.symm
  have hvId : a⁻¹ • Representation.IntertwiningMap.id π.representation = v := by
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  obtain ⟨b, hb⟩ := hv f
  exact ⟨b * a⁻¹, by rw [← smul_smul, hvId]; exact hb⟩

/-- Semisimplicity and scalar endomorphisms force irreducibility for a nonzero object. -/
theorem isIrreducible_of_semisimple_rank_endomorphism_le_one
    (hsem : π.representation.IsSemisimpleRepresentation)
    (hdim : Module.rank ℂ (π.representation.IntertwiningMap π.representation) ≤ 1) :
    π.IsIrreducible := by
  by_contra hred
  obtain ⟨f, hf⟩ :=
    RepresentedParabolic.exists_nonscalar_endomorphism_of_semisimple π hsem hred
  obtain ⟨c, hc⟩ := exists_scalar_of_rank_endomorphism_le_one π hdim (hom f)
  exact hf ⟨c, fun x => (congrArg (fun F => F x) hc).symm⟩

end Scalar

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (σ : SmoothRep.{0, uG, uV} ℂ M)

/-- Scalars sent by first adjointness to multiples of the actual evaluation counit. -/
def jacquetScalarMap :
    ℂ →ₗ[ℂ] (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
        σ.representation) :=
  (FirstAdjointness.equiv h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ).toLinearMap.comp
    (LinearMap.toSpanSingleton ℂ _ (Representation.IntertwiningMap.id
      ((normalizedInductionFunctor h hU).obj σ).representation))

theorem jacquetScalarMap_bijective
    [Nontrivial ((normalizedInductionFunctor h hU).obj σ)]
    (hdim : Module.rank ℂ (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
        σ.representation) ≤ 1) :
    Function.Bijective (jacquetScalarMap h hU hδ σ) := by
  let e := FirstAdjointness.equiv h hU hδ ((normalizedInductionFunctor h hU).obj σ) σ
  have hrank : Module.rank ℂ
      (((normalizedInductionFunctor h hU).obj σ).representation.IntertwiningMap
        ((normalizedInductionFunctor h hU).obj σ).representation) ≤ 1 := by
    rw [e.rank_eq]
    exact hdim
  constructor
  · intro a b hab
    have he : a • Representation.IntertwiningMap.id
        ((normalizedInductionFunctor h hU).obj σ).representation =
        b • Representation.IntertwiningMap.id
          ((normalizedInductionFunctor h hU).obj σ).representation := e.injective hab
    obtain ⟨x, hx⟩ := exists_ne (0 : (normalizedInductionFunctor h hU).obj σ)
    exact smul_left_injective ℂ hx (congrArg (fun F => F x) he)
  · intro f
    obtain ⟨c, hc⟩ := exists_scalar_of_rank_endomorphism_le_one
      ((normalizedInductionFunctor h hU).obj σ) hrank (e.symm f)
    exact ⟨c, (congrArg e hc).trans (e.apply_symm_apply f)⟩

/-- The actual Jacquet Hom space is identified with scalars by its evaluation counit,
when its dimension is at most one and induction is nonzero. -/
def jacquetScalarEquiv
    [Nontrivial ((normalizedInductionFunctor h hU).obj σ)]
    (hdim : Module.rank ℂ (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
        σ.representation) ≤ 1) :
    ℂ ≃ₗ[ℂ] (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
        σ.representation) :=
  LinearEquiv.ofBijective (jacquetScalarMap h hU hδ σ)
    (jacquetScalarMap_bijective h hU hδ σ hdim)

include hδ in
/-- Multiplicity one in `Hom(r(i σ), σ)`, together with semisimplicity, suffices;
irreducibility of the whole Jacquet module is not required. -/
theorem isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one
    [Nontrivial ((normalizedInductionFunctor h hU).obj σ)]
    (hsem : ((normalizedInductionFunctor h hU).obj σ).representation.IsSemisimpleRepresentation)
    (hdim : Module.rank ℂ (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
        σ.representation) ≤ 1) :
    ((normalizedInductionFunctor h hU).obj σ).IsIrreducible := by
  apply isIrreducible_of_semisimple_rank_endomorphism_le_one
    ((normalizedInductionFunctor h hU).obj σ) hsem
  rw [(FirstAdjointness.equiv h hU hδ
    ((normalizedInductionFunctor h hU).obj σ) σ).rank_eq]
  exact hdim

include hδ in
/-- The admissible unitary version uses the published semisimplicity theorem. -/
theorem isIrreducible_induction_of_unitary_jacquetHom_rank_le_one
    [Nontrivial σ] (hproj : Continuous h.projection)
    (hcof : CompactOpenCofinal G)
    (hadm : ((normalizedInductionFunctor h hU).obj σ).IsAdmissible)
    (hunitary : IsUnitarizable ((normalizedInductionFunctor h hU).obj σ).representation)
    (hdim : Module.rank ℂ (((jacquetFunctor h hU).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.IntertwiningMap
        σ.representation) ≤ 1) :
    ((normalizedInductionFunctor h hU).obj σ).IsIrreducible := by
  have := nontrivial_normalizedInduction h hU hproj σ
  exact isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one h hU hδ σ
    (admissibleUnitarySemisimplicity G hcof ((normalizedInductionFunctor h hU).obj σ)
      ((normalizedInductionFunctor h hU).obj σ).representation hadm hunitary) hdim

end Induction

end Langlands.Aubert.General
