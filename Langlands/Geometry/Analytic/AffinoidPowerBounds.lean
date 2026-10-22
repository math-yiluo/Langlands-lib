import Langlands.Geometry.Analytic.SpectralPowerBoundStatement
import Langlands.Geometry.Analytic.Affinoid
import Langlands.Geometry.Analytic.PowerBounds
import Langlands.Geometry.Analytic.TateGaussPoint

/-! # Power bounds for concrete affinoid presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- A monic relation over a Tate algebra with norm-bounded coefficients gives
bounded powers in any ultrametric target of a bounded algebra homomorphism.
The relation itself is input, not an assumed spectral theorem. -/
theorem hasBoundedPowers_of_tate_monic_relation
    {A : Type v} [NormedCommRing A] [IsUltrametricDist A] [Algebra K A]
    {d : ℕ} (φ : BoundedAlgHom K (StrictTateAlgebra (Fin d) K) A)
    (a : A) (p : Polynomial (StrictTateAlgebra (Fin d) K))
    (hp : p.Monic) (ha : p.eval₂ φ.toAlgHom.toRingHom a = 0)
    (hcoeff : ∀ i, ‖p.coeff i‖ ≤ 1) : HasBoundedPowers a := by
  let : Nontrivial (StrictTateAlgebra (Fin d) K) :=
    ⟨⟨0, 1, fun h => by have hn := congrArg norm h; simp at hn⟩⟩
  let S := normUnitBallSubring (StrictTateAlgebra (Fin d) K)
  have hlift : p ∈ Polynomial.lifts S.subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts p).mpr
    intro i
    exact ⟨⟨p.coeff i, by change ‖p.coeff i‖ ≤ 1; exact hcoeff i⟩, rfl⟩
  obtain ⟨q, hq, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  apply hasBoundedPowers_of_monic_relation
    (φ.toAlgHom.toRingHom.comp S.subtype) a q hmonic
  · rw [← Polynomial.eval₂_map, hq]
    exact ha
  · obtain ⟨C, hC, hc⟩ := φ.bounded
    refine ⟨C, hC, fun s => ?_⟩
    have hs := s.property
    change ‖s.val‖ ≤ 1 at hs
    exact (hc s.val).trans
      ((mul_le_mul_of_nonneg_left hs hC.le).trans_eq (mul_one C))

namespace PresentedStrictAffinoidAlgebra

/-- If the coefficient norm is trivial, every element of the actual quotient
has norm at most one. No spectral comparison is required. -/
theorem norm_le_one_of_scalar_norm_le_one (P : PresentedStrictAffinoidAlgebra K)
    (hK : ∀ c : K, ‖c‖ ≤ 1) (a : P) : ‖a‖ ≤ 1 := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K P a
  apply (Ideal.Quotient.norm_mk_le P.ideal f).trans
  exact (StrictTateAlgebra.norm_le_iff (Fin P.arity) K f zero_le_one).mpr
    (fun i => hK (MvPowerSeries.coeff i (StrictTateAlgebra.series _ _ f)))

/-- This closes the trivial-valuation case of the assigned spectral theorem
for every closed-ideal quotient, including nonreduced and zero quotients. -/
theorem hasBoundedPowers_of_scalar_norm_le_one (P : PresentedStrictAffinoidAlgebra K)
    (hK : ∀ c : K, ‖c‖ ≤ 1) (a : P) : HasBoundedPowers a :=
  ⟨1, zero_lt_one, fun n => norm_le_one_of_scalar_norm_le_one P hK (a ^ n)⟩

/-- The full target holds over a trivially valued coefficient field. -/
theorem spectralPowerBound_of_scalar_norm_le_one [CompleteSpace K]
    (hK : ∀ c : K, ‖c‖ ≤ 1) : SpectralPowerBoundStatement K :=
  fun P a _ => hasBoundedPowers_of_scalar_norm_le_one P hK a

end PresentedStrictAffinoidAlgebra

end Langlands.Analytic
