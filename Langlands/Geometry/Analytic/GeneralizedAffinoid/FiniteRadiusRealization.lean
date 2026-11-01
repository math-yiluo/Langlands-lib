import Langlands.Geometry.Analytic.GeneralizedAffinoid.RadiusRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory
import Mathlib.Data.Fintype.EquivFin

/-! # Simultaneous radius realization for finite chart families -/

noncomputable section

universe u v

namespace Langlands.Analytic

/-- A finite family in an independent universe can be realized in a complete
extension field in the universe of the coefficient field. -/
structure FiniteRadiusRealization (K : Type u) [NormedField K]
    {σ : Type v} (t : σ → ℝ) where
  L : Type u
  [instNormedField : NormedField L]
  [instUltrametric : IsUltrametricDist L]
  [instComplete : CompleteSpace L]
  ι : K →+* L
  norm_ι : ∀ a, ‖ι a‖ = ‖a‖
  c : σ → L
  norm_c : ∀ i, ‖c i‖ = t i
  π : L →+ K
  π_ι_mul : ∀ a x, π (ι a * x) = a * π x
  π_one : π 1 = 1
  bound : ℝ
  bound_pos : 0 < bound
  norm_π_le : ∀ x, ‖π x‖ ≤ bound * ‖x‖

namespace FiniteRadiusRealization

attribute [instance] instNormedField instUltrametric instComplete

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type v} [Finite σ]

/-- Enumerating the finite index set before realizing its radii keeps the field
universe independent of the universe of that set. -/
theorem nonempty (t : σ → ℝ) (ht : ∀ i, 0 < t i) :
    Nonempty (FiniteRadiusRealization K t) := by
  let := Fintype.ofFinite σ
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  obtain ⟨R⟩ := RadiusRealization.nonempty (K := K) (Fintype.card σ)
    (fun j => t (e.symm j)) (fun j => ht (e.symm j))
  exact ⟨{
    L := R.L
    ι := R.ι
    norm_ι := R.norm_ι
    c := fun i => R.c (e i)
    norm_c := fun i => by simpa using R.norm_c (e i)
    π := R.π
    π_ι_mul := R.π_ι_mul
    π_one := R.π_one
    bound := R.bound
    bound_pos := R.bound_pos
    norm_π_le := R.norm_π_le }⟩

omit [IsUltrametricDist K] [CompleteSpace K] [Finite σ] in
theorem c_ne_zero {t : σ → ℝ} (R : FiniteRadiusRealization K t)
    (ht : ∀ i, 0 < t i) (i : σ) : R.c i ≠ 0 := by
  rw [← norm_ne_zero_iff, R.norm_c]
  exact (ht i).ne'

end FiniteRadiusRealization

namespace PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K} {I : Type v}

/-- All base and relative coordinates in a family of rational charts. -/
abbrev FamilyRadiusIndex (D : I → RationalChart K A) :=
  Fin A.arity ⊕ (Σ i : I, Fin (D i).arity)

/-- The prescribed norm for each base or relative coordinate. -/
def familyRadius (D : I → RationalChart K A) : FamilyRadiusIndex D → ℝ
  | .inl j => A.polyradius j
  | .inr ⟨i, j⟩ => (D i).radii j

theorem familyRadius_pos (D : I → RationalChart K A) (j : FamilyRadiusIndex D) :
    0 < familyRadius D j := by
  rcases j with j | ⟨i, j⟩
  · exact A.polyradius.positive j
  · exact (D i).radii.positive j

/-- One complete extension realizes every base and chart radius, even when the
finite chart index type lives in an independent universe. -/
theorem familyRadiusRealization_nonempty [CompleteSpace K] [Finite I]
    (D : I → RationalChart K A) :
    Nonempty (FiniteRadiusRealization K (familyRadius D)) :=
  FiniteRadiusRealization.nonempty _ (familyRadius_pos D)

end PresentedAffinoidAlgebra.RationalChart

end Langlands.Analytic
