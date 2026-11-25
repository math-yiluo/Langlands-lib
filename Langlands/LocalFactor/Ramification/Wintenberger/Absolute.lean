import Langlands.LocalFactor.Ramification.Wintenberger.Finite
import Langlands.LocalFactor.Ramification.Wintenberger.FieldClass
import FontaineWintenberger.Ramification.Infinite.Basic
import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteStatement

/-!
# Absolute upper ramification groups of the two libraries

For a complete, ultrametric, locally compact base `K₀` whose norm induces its valuative relation,
a finite normed extension `K` of `K₀` that is complete and discretely valued, and a separable
closure `Ω` of `K`, the FontaineWintenberger filtration `upperRamificationGroupInfinite K Ω` is
the Library's `Local.absoluteUpperRamificationGroup K₀ K Ω hbase`. The p-adic filtration
`Padic.absoluteUpperRamificationGroup F` and the filtration
`Local.localAbsoluteUpperRamificationGroup K Ω` of a Mathlib local field are the two
specializations. As a consequence, the absolute filtration of every Mathlib local field maps
onto the finite upper filtrations (`Local.AbsoluteUpperFiniteImage`).
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe u₀ uK

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀] [CompleteSpace K₀]
  [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)

section Absolute

universe uΩ

variable (K : Type uK) [NontriviallyNormedField K] [NormedAlgebra K₀ K]
  [FontaineWintenberger.IsCompleteDiscreteValuedField K] [FiniteDimensional K₀ K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω] [IsSepClosure K Ω]

/-- **The absolute upper filtrations of the two libraries agree**, on the Library's general layer.
Both are intersections over the finite Galois subextensions of the preimages of the finite upper
groups, and these agree term by term. -/
theorem upperRamificationGroupInfinite_eq_absolute (v : ℝ) :
    FontaineWintenberger.upperRamificationGroupInfinite K Ω v =
      Local.absoluteUpperRamificationGroup K₀ K Ω hbase v := by
  unfold FontaineWintenberger.upperRamificationGroupInfinite Local.absoluteUpperRamificationGroup
  refine iInf_congr fun L => ?_
  have : FiniteDimensional K₀ L := FiniteDimensional.trans K₀ K L
  rw [upperRamificationGroup_spectral_eq_canonical K₀ hbase L K v]
  rfl

end Absolute


universe u v

/-- The norm of `Padic p` induces its valuative relation. -/
theorem padicBaseNorm_compatible (p : ℕ) [Fact p.Prime] (a b : Padic p) :
    ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b := by
  change ‖a‖ ≤ ‖b‖ ↔ Padic.mulValuation a ≤ Padic.mulValuation b
  simp only [← not_lt, Padic.norm_lt_norm_iff_mulValuation_lt]

/-- The p-adic case: for a `p`-adic field with its canonical spectral norm, the
FontaineWintenberger filtration of its algebraic closure is the Library's p-adic filtration. -/
theorem upperRamificationGroupInfinite_eq_padic {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (v : ℝ) :
    letI := F.canonicalNormedField
    haveI := (padicField_isPerfectResidueLocalField F).toIsCompleteDiscreteValuedField
    FontaineWintenberger.upperRamificationGroupInfinite F.Carrier (AlgebraicClosure F.Carrier) v =
      Padic.absoluteUpperRamificationGroup F v := by
  let := F.canonicalNormedField
  let := F.canonicalNormedAlgebra
  have := (padicField_isPerfectResidueLocalField F).toIsCompleteDiscreteValuedField
  have : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact upperRamificationGroupInfinite_eq_absolute (Padic p) (padicBaseNorm_compatible p)
    F.Carrier (AlgebraicClosure F.Carrier) v

/-- The Library's normed-field adapter of a Mathlib local field induces its valuative relation. -/
theorem localBaseNorm_compatible (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (a b : K) :
    letI := LocalGalois.localNormedField K
    ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b :=
  (LocalGalois.localNormedField_le K a b).trans (ValuativeRel.valuation K).vle_iff_le.symm

/-- The case of a Mathlib nonarchimedean local field, in either characteristic, with the Library's
normed-field adapter and any separable closure. -/
theorem upperRamificationGroupInfinite_eq_local (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ℝ) :
    letI := LocalGalois.localNormedField K
    haveI := (localField_isPerfectResidueLocalField K).toIsCompleteDiscreteValuedField
    FontaineWintenberger.upperRamificationGroupInfinite K Ω w =
      Local.localAbsoluteUpperRamificationGroup K Ω w := by
  let := LocalGalois.localNormedField K
  have := (localField_isPerfectResidueLocalField K).toIsCompleteDiscreteValuedField
  have := LocalGalois.localNormedField_ultrametric K
  have := LocalGalois.localNormedField_complete K
  exact upperRamificationGroupInfinite_eq_absolute K (localBaseNorm_compatible K) K Ω w

/-- **Exact finite images for every Mathlib local field.** The absolute upper filtration of a
separable closure maps onto the finite upper filtration of every finite Galois subextension, on
Serre's domain `-1 ≤ v`. -/
theorem localAbsoluteUpperFiniteImage (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] :
    Local.AbsoluteUpperFiniteImage K Ω := by
  intro L w hw
  let := LocalGalois.localNormedField K
  have := localField_isPerfectResidueLocalField K
  have := LocalGalois.localNormedField_ultrametric K
  have := LocalGalois.localNormedField_complete K
  rw [← upperRamificationGroupInfinite_eq_local K Ω w]
  change (FontaineWintenberger.upperRamificationGroupInfinite K Ω w).map
    (AlgEquiv.restrictNormalHom L) = _
  rw [FontaineWintenberger.map_upperRamificationGroupInfinite K Ω L w hw]
  exact upperRamificationGroup_spectral_eq_canonical K (localBaseNorm_compatible K) L K w

end Langlands.Ramification.Wintenberger
