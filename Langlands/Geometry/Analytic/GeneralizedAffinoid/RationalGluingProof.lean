import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRadiusRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNormalizationOverlap
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartScalarRetraction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalGluingStatement
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteIndexRationalGluing

/-! # Scalar rational descent for arbitrary positive polyradii -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type w} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (A : PresentedAffinoidAlgebra K)
  {I : Type v} [Finite I] (D : I → RationalChart K A)
  (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin A.arity → L} (hc : ∀ j, ‖c j‖ = A.polyradius j)
  {τ : ∀ i, Fin (D i).arity → L} (hτ : ∀ i j, ‖τ i j‖ = (D i).radii j)
  (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {B : ℝ} (hB : 0 ≤ B) (hπB : ∀ x, ‖π x‖ ≤ B * ‖x‖) (hπ1 : π 1 = 1)

omit [CompleteSpace K] in
include hπ hB hπB hπ1 in
private theorem scalarDescent_of_compatibleMaps
    (F : ∀ i, BoundedRingHom (D i).algebra
      ((D i).scalarNormalizedStrict ι hι hc (hτ i)).algebra)
    (hF : ∀ i a, F i ((D i).baseMap a) =
      ((D i).scalarNormalizedStrict ι hι hc (hτ i)).baseMap
        (strictBaseChangeHom A ι hι hc a))
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus)
    (s : ∀ i, (D i).algebra)
    (hcompat : ∀ i j,
      (StrictTestDomain.RationalData.interLeft
        ((D i).scalarNormalizedStrict ι hι hc (hτ i))
        ((D j).scalarNormalizedStrict ι hι hc (hτ j))).restriction (F i (s i)) =
      (StrictTestDomain.RationalData.interRight
        ((D i).scalarNormalizedStrict ι hι hc (hτ i))
        ((D j).scalarNormalizedStrict ι hι hc (hτ j))).restriction (F j (s j))) :
    ∃! a : A, ∀ i, (D i).baseMap a = s i := by
  let Q := strictBaseChange A ι hι hc
  let ψ := strictBaseChangeBoundedHom A ι hι hc
  let E := fun i => (D i).scalarNormalizedStrict ι hι hc (hτ i)
  have hcov : ∀ x : BanachSpectrum Q, ∃ i, x ∈ (E i).locus :=
    normalizedStrict_cover Q ψ D τ hτ hcover
  obtain ⟨b, hb, hu⟩ := StrictTestDomain.wholeSpectrumRationalGluing_finiteIndex
    L Q I E hcov (fun i => F i (s i)) hcompat
  let R := strictBaseChangeRetraction A ι hι hc π hπ hB hπB
  refine ⟨R b, ?_, ?_⟩
  · intro i
    calc
      (D i).baseMap (R b) =
          (D i).scalarRetraction ι hι hc (hτ i) π hπ hB hπB ((E i).baseMap b) :=
        ((D i).scalarRetraction_baseMap ι hι hc (hτ i) π hπ hB hπB b).symm
      _ = (D i).scalarRetraction ι hι hc (hτ i) π hπ hB hπB (F i (s i)) :=
        congrArg ((D i).scalarRetraction ι hι hc (hτ i) π hπ hB hπB) (hb i)
      _ = s i :=
        (D i).scalarRetraction_map ι hι hc (hτ i) π hπ hB hπB hπ1
          (F i) (hF i) (s i)
  · intro a ha
    have hea : ∀ i, (E i).baseMap (strictBaseChangeHom A ι hι hc a) = F i (s i) := by
      intro i
      exact (hF i a).symm.trans (congrArg (F i) (ha i))
    calc
      a = R (strictBaseChangeHom A ι hι hc a) :=
        (strictBaseChangeRetraction_strictBaseChangeHom A ι hι hc π hπ hB hπB hπ1 a).symm
      _ = R b := congrArg R (hu _ hea)

/-- Compatible scalar sections on a finite positive-radius rational cover of
the whole spectrum descend uniquely to the actual original affinoid algebra. -/
theorem wholeSpectrumRationalGluing :
    WholeSpectrumRationalGluingStatement.{u, v} := by
  intro K _ _ _ A I _ D hcover s hcompat
  obtain ⟨R⟩ := familyRadiusRealization_nonempty D
  let c : Fin A.arity → R.L := fun j => R.c (.inl j)
  have hc : ∀ j, ‖c j‖ = A.polyradius j := fun j => R.norm_c (.inl j)
  let τ : ∀ i, Fin (D i).arity → R.L := fun i j => R.c (.inr ⟨i, j⟩)
  have hτ : ∀ i j, ‖τ i j‖ = (D i).radii j := fun i j => R.norm_c (.inr ⟨i, j⟩)
  let Q := strictBaseChange A R.ι R.norm_ι hc
  let ψ := strictBaseChangeBoundedHom A R.ι R.norm_ι hc
  have hψ : ∀ a, ‖ψ a‖ ≤ ‖a‖ := norm_strictBaseChangeHom_le A R.ι R.norm_ι hc
  apply scalarDescent_of_compatibleMaps A D R.ι R.norm_ι hc hτ
    R.π R.π_ι_mul R.bound_pos.le R.norm_π_le R.π_one
    (fun i => (D i).normalizedStrictMap Q ψ hψ (τ i) (hτ i))
    (fun i a => (D i).normalizedStrictMap_baseMap Q ψ hψ (τ i) (hτ i) a)
    hcover s
  intro i j
  exact normalizedStrictMap_compatible (D i) (D j) Q ψ hψ
    (τ i) (τ j) (hτ i) (hτ j) (s i) (s j) (hcompat i j)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
