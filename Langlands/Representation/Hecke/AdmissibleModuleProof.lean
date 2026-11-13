import Langlands.Representation.Hecke.AdmissibleModuleStatement
import Langlands.Representation.Hecke.FiniteRankAction

/-!
# Admissibility of representations and their Hecke modules

Renard III.1.7, printed p.62 / PDF p.68.
-/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory Langlands.Algebra

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The intrinsic complex scalars on an idempotent-fixed part agree with the
original representation scalars, so its actual inclusion is complex linear. -/
def heckeFixedPartInclusion (e : Idempotent (HeckeAlgebra μ)) :
    letI := heckeNonUnitalModule μ ρ hρ
    letI := NonUnitalModuleCorner.complexModule (Homomorphism.isIdempotented μ)
      (heckeNonUnitalModule_isNondegenerate μ ρ hρ) e
    NonUnitalModuleCorner.FixedPart e V →ₗ[ℂ] V := by
  letI := heckeNonUnitalModule μ ρ hρ
  letI := NonUnitalModule.ofLinearEndHom_isScalarTower (heckeAction μ ρ hρ)
  letI := NonUnitalModuleCorner.complexModule (Homomorphism.isIdempotented μ)
    (heckeNonUnitalModule_isNondegenerate μ ρ hρ) e
  exact
    { toFun := fun x => x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun c x =>
        NondegenerateScalars.scalarMul_eq_of_compatible ℂ
          (heckeNonUnitalModule_isNondegenerate μ ρ hρ) c x.val }

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
include hρ in
/-- Compact open subgroups suffice to test admissibility of a smooth representation. -/
theorem isAdmissible_iff_compactOpen_fixedVectors :
    IsAdmissible ρ ↔ ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := by
  constructor
  · intro ha K _
    exact ha.2 K
  · intro h
    refine ⟨hρ, fun N => ?_⟩
    obtain ⟨K, hK, hKN⟩ :=
      compactOpenSubgroupBasis G (N : Set G) (N.isOpen.mem_nhds N.one_mem)
    let := h K hK
    exact Submodule.finiteDimensional_of_le
      (fixedVectors_antitone ρ (show K.toSubgroup ≤ N.toSubgroup from hKN))

/-- Renard III.1.7: the compact-open criterion and admissibility of the
corresponding nondegenerate Hecke module, with the published intrinsic scalars. -/
theorem admissibleIffHeckeAdmissible : AdmissibleIffHeckeAdmissibleStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _ V _ _ ρ hρ
  have hcompact := isAdmissible_iff_compactOpen_fixedVectors (ρ := ρ) hρ
  refine ⟨hcompact, ?_⟩
  let := heckeNonUnitalModule μ ρ hρ
  constructor
  · intro ha e
    let := NonUnitalModuleCorner.complexModule (Homomorphism.isIdempotented μ)
      (heckeNonUnitalModule_isNondegenerate μ ρ hρ) e
    let := heckeAction_finiteDimensional_range μ ρ ha (e : HeckeAlgebra μ)
    let inclusion : NonUnitalModuleCorner.FixedPart e V →ₗ[ℂ]
        LinearMap.range (heckeAction μ ρ hρ (e : HeckeAlgebra μ)) :=
      (heckeFixedPartInclusion μ ρ hρ e).codRestrict _ fun x =>
        ⟨x.val, x.property⟩
    apply FiniteDimensional.of_injective inclusion
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun z : LinearMap.range (heckeAction μ ρ hρ (e : HeckeAlgebra μ)) => (z : V)) h
  · intro ha
    apply hcompact.mpr
    intro K hK
    let e : Idempotent (HeckeAlgebra μ) :=
      ⟨HeckeAlgebra.normalizedIndicator μ K hK,
        HeckeAlgebra.normalizedIndicator_idempotent μ K hK⟩
    let := NonUnitalModuleCorner.complexModule (Homomorphism.isIdempotented μ)
      (heckeNonUnitalModule_isNondegenerate μ ρ hρ) e
    let := ha e
    have hmem (x : NonUnitalModuleCorner.FixedPart e V) :
        x.val ∈ fixedVectors ρ K.toSubgroup := by
      have hx : heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) x.val =
          x.val := x.property
      rw [← hx]
      exact heckeAction_normalizedIndicator_mem μ ρ hρ K hK x.val
    let inclusion : NonUnitalModuleCorner.FixedPart e V →ₗ[ℂ]
        fixedVectors ρ K.toSubgroup :=
      (heckeFixedPartInclusion μ ρ hρ e).codRestrict _ hmem
    apply FiniteDimensional.of_surjective inclusion
    intro x
    exact ⟨⟨x.val, heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK x.property⟩,
      Subtype.ext rfl⟩

end Langlands.Hecke
