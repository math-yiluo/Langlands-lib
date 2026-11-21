import Langlands.Representation.Archimedean.MixedOrbitClosure
import Langlands.Representation.Archimedean.RealCartanSquareSum
import Langlands.Representation.Archimedean.SmoothCompactPolynomialAnnihilation
import Langlands.Representation.Archimedean.CompactFiniteClosure
import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-! # Algebraic irreducibility of genuine compact-finite smooth vectors for real `GL_n` -/

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealSmoothIrreducible

open Langlands.Global Langlands.Global.ArchimedeanGL

/-- A vector with finite orbit span under the matrix orthogonal group has finite orbit span
under the corresponding subgroup of actual units. -/
theorem isFiniteVector_subgroup_of_mem_smoothKFinite (n : ℕ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
    {w : DerivativeSmoothVectors (matrixModel ℝ n) R} (hw : w ∈ smoothKFinite ℝ n R) :
    FiniteVectors.IsFiniteVector
      (DerivativeSmoothVectors.subgroupRepresentation R (unitaryCompact ℝ n)) w := by
  have hw' : FiniteVectors.IsFiniteVector
      ((DerivativeSmoothVectors.representation (matrixModel ℝ n) R).comp Unitary.toUnits) w := hw
  let : Module.Finite ℂ (FiniteVectors.orbitSpan
      ((DerivativeSmoothVectors.representation (matrixModel ℝ n) R).comp Unitary.toUnits) w) := hw'
  apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan
    ((DerivativeSmoothVectors.representation (matrixModel ℝ n) R).comp Unitary.toUnits) w)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  refine Submodule.subset_span ⟨⟨(k : Langlands.GeneralLinear n ℝ),
    (k.prop : ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) ∈
      Matrix.unitaryGroup (Fin n) ℝ)⟩, ?_⟩
  change DerivativeSmoothVectors.representation (matrixModel ℝ n) R (Unitary.toUnits _) w =
    DerivativeSmoothVectors.representation (matrixModel ℝ n) R (k : Langlands.GeneralLinear n ℝ) w
  congr 2
  exact Units.ext rfl

/-- A subspace of genuine compact-finite smooth vectors of an irreducible admissible Banach
representation of actual `GL_n(ℝ)` that is stable under the orthogonal group and under every
genuine derivative is either zero or contains all compact-finite smooth vectors. -/
theorem eq_bot_or_smoothKFinite_le (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
    (hR : IsContinuousRepresentation R) (hirr : IsTopologicallyIrreducible R)
    (hadm : IsAdmissible R (unitaryCompact ℝ n))
    (W : Submodule ℂ (DerivativeSmoothVectors (matrixModel ℝ n) R))
    (hWV : W ≤ smoothKFinite ℝ n R)
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ w ∈ W,
      DerivativeSmoothVectors.representation (matrixModel ℝ n) R (Unitary.toUnits k) w ∈ W)
    (hWX : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W,
      DerivativeSmoothVectors.operator (matrixModel ℝ n) R X w ∈ W) :
    W = ⊥ ∨ smoothKFinite ℝ n R ≤ W := by
  let Kc := unitaryCompact ℝ n
  let ε := DerivativeSmoothVectors.derivativeCLM (matrixModel ℝ n) R []
  have hεinj : Function.Injective ε := by
    intro a b h
    apply (DerivativeSmoothVectors.toSmooth (matrixModel ℝ n) R).injective
    exact Subtype.ext h
  have hWK' : ∀ k ∈ Kc, ∀ w ∈ W,
      DerivativeSmoothVectors.representation (matrixModel ℝ n) R k w ∈ W := by
    intro k hk w hw
    have h := hWK ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w hw
    have hk' : (Unitary.toUnits ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
        Langlands.GeneralLinear n ℝ) = k := Units.ext rfl
    rwa [hk'] at h
  let Ω := MixedOrbit.transportedCartanSquareSum ℚ n (rationalMixedMatrixEquiv n) R
  have hΩ : ∀ (k : Kc) (w : DerivativeSmoothVectors (matrixModel ℝ n) R),
      Ω (DerivativeSmoothVectors.representation (matrixModel ℝ n) R (k : Langlands.GeneralLinear n ℝ) w) =
        DerivativeSmoothVectors.representation (matrixModel ℝ n) R (k : Langlands.GeneralLinear n ℝ)
          (Ω w) :=
    fun k w => RealCartan.transportedCartanSquareSum_representation n R k.prop w
  have hadm' := DerivativeSmoothVectors.isAdmissible_of_norm (matrixModel ℝ n) R Kc hadm
  have hpoly : ∀ w ∈ W, ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval Ω p w = 0 :=
    fun w hw => DerivativeSmoothVectors.exists_monic_aeval_eq_zero_of_isFiniteVector R Kc hR
      hadm' Ω hΩ (isFiniteVector_subgroup_of_mem_smoothKFinite n R (hWV hw))
  have hclos := MixedOrbit.representation_mem_closure_of_stable ℚ n (rationalMixedMatrixEquiv n)
    R Kc hR W (fun X w hw => hWX _ w hw) hWK' hpoly
    (RealCartan.exists_unitaryCompact_mem_connectedComponent n)
  let C := (W.map (ε : _ →ₗ[ℂ] E)).topologicalClosure
  have hCinv : ∀ g : Langlands.GeneralLinear n ℝ, ∀ y ∈ C, R g y ∈ C := by
    intro g y hy
    have hle : W.map (ε : _ →ₗ[ℂ] E) ≤ C.comap ((R g : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
      rintro _ ⟨w, hw, rfl⟩
      exact hclos g hw
    have hclosed : IsClosed ((C.comap ((R g : E →L[ℂ] E) : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) :=
      (Submodule.isClosed_topologicalClosure _).preimage (R g).continuous
    exact Submodule.topologicalClosure_minimal _ hle hclosed hy
  rcases hirr.2 C (Submodule.isClosed_topologicalClosure _) hCinv with hC | hC
  · left
    apply (Submodule.eq_bot_iff W).mpr
    intro w hw
    have h : ε w ∈ C := Submodule.le_topologicalClosure _ ⟨w, hw, rfl⟩
    rw [hC, Submodule.mem_bot] at h
    exact hεinj (h.trans (map_zero ε).symm)
  · right
    intro v hv
    let : MeasurableSpace Kc := borel Kc
    have : BorelSpace Kc := ⟨rfl⟩
    let ν : Measure Kc := Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩
    have : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
    let T : (DerivativeSmoothVectors.subgroupRepresentation R Kc).IntertwiningMap
        (normCompactRepresentation Kc R) :=
      LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (ε : _ →ₗ[ℂ] E) (fun _ _ => rfl)
    let W' : Subrepresentation (normCompactRepresentation Kc R) :=
      { toSubmodule := W.map (ε : _ →ₗ[ℂ] E)
        apply_mem_toSubmodule := by
          rintro k _ ⟨w, hw, rfl⟩
          exact ⟨_, hWK' k k.prop w hw, rfl⟩ }
    have hW' : ∀ y ∈ W'.toSubmodule,
        FiniteVectors.IsFiniteVector (normCompactRepresentation Kc R) y := by
      rintro _ ⟨w, hw, rfl⟩
      exact (isFiniteVector_subgroup_of_mem_smoothKFinite n R (hWV hw)).map T
    have hvC : ε v ∈ W'.toSubmodule.topologicalClosure := by
      change ε v ∈ C
      rw [hC]
      exact Submodule.mem_top
    have hvK : FiniteVectors.IsFiniteVector (normCompactRepresentation Kc R) (ε v) :=
      (isFiniteVector_subgroup_of_mem_smoothKFinite n R hv).map T
    obtain ⟨w, hw, he⟩ := mem_compactSubrepresentation_of_mem_closure Kc R hR ν hadm W' hW' hvC hvK
    rwa [hεinj he] at hw

end Langlands.Archimedean.RealSmoothIrreducible
