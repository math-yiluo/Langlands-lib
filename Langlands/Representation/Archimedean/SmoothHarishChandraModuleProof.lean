import Langlands.Representation.Archimedean.RealSmoothGKModule
import Langlands.Representation.Archimedean.RealSmoothKFiniteIrreducible
import Langlands.Representation.Archimedean.OrthogonalCompactFiniteDensity
import Langlands.Representation.Archimedean.CompactFiniteSmoothness
import Langlands.Representation.Archimedean.RealCompactTraceSeparation
import Langlands.Representation.Archimedean.SmoothHarishChandraModuleStatement

/-! # Proof: the Harish-Chandra module of a real irreducible admissible Hilbert representation -/

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe uH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- An irreducible admissible representation on a nonzero complete complex Hilbert space has a
nonzero genuine compact-finite smooth vector. -/
theorem smoothHilbertKFinite_nontrivial (n : ℕ) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
    (hR : IsContinuousRepresentation R) (hH : Nontrivial H)
    (hadm : IsAdmissible R (unitaryCompact ℝ n)) :
    Nontrivial (smoothHilbertKFinite ℝ n R) := by
  let R' : Matrix.unitaryGroup (Fin n) ℝ →* (H →L[ℂ] H) := R.comp Unitary.toUnits
  have hR' : IsContinuousRepresentation R' :=
    hR.comp ((continuous_unitary_toUnits (N := n) (F := ℝ)).prodMap continuous_id)
  have hdense := dense_finiteVectors_orthogonal n
    (Measure.haar : Measure (Matrix.unitaryGroup (Fin n) ℝ)) R' hR'
  obtain ⟨x, hx0, hxK⟩ : ∃ x : H, x ≠ 0 ∧ FiniteVectors.IsFiniteVector
      (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R') x := by
    by_contra hnone
    push Not at hnone
    obtain ⟨y, hy⟩ := exists_ne (0 : H)
    have hsub : ((FiniteVectors.subrepresentation
        (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R')).toSubmodule : Set H) ⊆
        {0} := fun z hz => by
      by_contra hz0
      exact hnone z hz0 hz
    have hmem := closure_mono hsub (hdense y)
    rw [closure_singleton] at hmem
    exact hy hmem
  let Kc := unitaryCompact ℝ n
  have hxKc : FiniteVectors.IsFiniteVector (normCompactRepresentation Kc R) x := by
    have : Module.Finite ℂ (FiniteVectors.orbitSpan
        (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R') x) := hxK
    apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan
      (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp R') x)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ),
      k.prop⟩, ?_⟩
    change R (Unitary.toUnits _) x = R (k : Langlands.GeneralLinear n ℝ) x
    congr 2
    exact Units.ext rfl
  let : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
  have : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
  have : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) :=
    Units.isOpenEmbedding_val.locallyCompactSpace
  let : MeasurableSpace Kc := borel Kc
  have : BorelSpace Kc := ⟨rfl⟩
  let ν : Measure Kc := Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩
  have : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  have hs := isSmoothVector_of_normCompactFinite
    (Measure.haar : Measure (Langlands.GeneralLinear n ℝ)) Kc ν R hR hadm x hxKc
  obtain ⟨y, hy⟩ := exists_smoothHilbertKFinite_of_norm n R hs hxKc
  refine ⟨⟨y, 0, fun h => hx0 ?_⟩⟩
  rw [← hy, h]
  exact map_zero _

/-- **Proof of `RealSmoothHilbertHarishChandraModuleStatement`.** -/
theorem realSmoothHilbertHarishChandraModule :
    RealSmoothHilbertHarishChandraModuleStatement.{uH} := by
  intro r H _ _ _ R hR
  obtain ⟨hcont, hirr, hadm⟩ := hR
  let V := smoothKFinite ℝ (r + 1) R
  refine ⟨smoothKFiniteRepresentation ℝ (r + 1) R, RealSmoothGK.lieAction (r + 1) R hcont,
    RealSmoothGK.isRealGKModule (r + 1) R hcont, ?_,
    isAdmissibleGKModule_smoothKFinite ℝ (r + 1) R hadm,
    RealSmoothGK.isSmoothGKIntertwiner (r + 1) R hcont⟩
  refine ⟨smoothHilbertKFinite_nontrivial (r + 1) R hcont hirr.1 hadm, fun W hWK hWX => ?_⟩
  rcases RealSmoothIrreducible.eq_bot_or_smoothKFinite_le (r + 1) R hcont hirr hadm
      (W.map V.subtype) (Submodule.map_subtype_le _ _)
      (by
        rintro k _ ⟨u, hu, rfl⟩
        exact ⟨_, hWK k u hu, rfl⟩)
      (by
        rintro X _ ⟨u, hu, rfl⟩
        exact ⟨_, hWX ((1 : ℂ) ⊗ₜ X) u hu, RealSmoothGK.lieAction_one_tmul (r + 1) R hcont X u⟩)
    with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem : (u : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R) ∈ W.map V.subtype :=
      ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · right
    rw [eq_top_iff]
    intro u _
    obtain ⟨u', hu', he⟩ := h u.prop
    rwa [Subtype.ext he] at hu'

example : RealSmoothHilbertHarishChandraModuleStatement.{uH} :=
  realSmoothHilbertHarishChandraModule

end Langlands.Archimedean
