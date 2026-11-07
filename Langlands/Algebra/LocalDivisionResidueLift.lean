import Langlands.Algebra.LocalDivisionSubfieldHensel
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Valuation.Integral

/-! Integral lifts of residue minimal polynomials inside the original division algebra. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance : Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

section Embedded

variable {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- Original integral scalars inside an actual embedded field. -/
def localDivisionSubfieldBaseIntegerMap :
    𝒪[K] →+* (localDivisionSubfieldValuation K D ι).integer where
  toFun a := ⟨algebraMap K L a.val, by
    change localReducedNormValuation K D (ι (algebraMap K L a.val)) ≤ 1
    rw [ι.commutes, localReducedNormValuation_algebraMap]
    exact pow_le_one₀ zero_le a.prop⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

/-- Scalar reduction commutes with the original subfield residue inclusion. -/
theorem localDivisionSubfieldBaseIntegerMap_reduction (a : 𝒪[K]) :
    localDivisionSubfieldResidueMap K D ι
        (DivisionValuation.reduction _ (localDivisionSubfieldBaseIntegerMap K D ι a)) =
      localDivisionBaseReduction K D a := by
  rw [localDivisionSubfieldResidueMap_reduction]
  apply congrArg (DivisionValuation.reduction _)
  exact Subtype.ext (ι.commutes a.val)

/-- A simple residue root of an original scalar polynomial lifts in any full-residue subfield. -/
theorem localDivisionSubfield_lift_base_polynomial [FiniteDimensional K L]
    (hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι))
    (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (z : DivisionValuation.Residue (localReducedNormValuation K D))
    (hroot : f.eval₂ (localDivisionBaseReduction K D) z = 0)
    (hder : f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0) :
    ∃ b : (localDivisionSubfieldValuation K D ι).integer,
      f.eval₂ (localDivisionSubfieldBaseIntegerMap K D ι) b = 0 ∧
        localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction _ b) = z := by
  let φ := localDivisionSubfieldBaseIntegerMap K D ι
  let ρ := DivisionValuation.reduction (localDivisionSubfieldValuation K D ι)
  let τ := localDivisionSubfieldResidueMap K D ι
  have hcomp : τ.comp (ρ.comp φ) = localDivisionBaseReduction K D := by
    ext a
    exact localDivisionSubfieldBaseIntegerMap_reduction K D ι a
  obtain ⟨z₀, hz₀⟩ := hsurj z
  change τ z₀ = z at hz₀
  have hroot₀ : (f.map φ).eval₂ ρ z₀ = 0 := by
    apply τ.injective
    rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂, hcomp, hz₀, hroot]
  have hder₀ : (f.map φ).derivative.eval₂ ρ z₀ ≠ 0 := by
    intro h
    apply hder
    have hh := congrArg τ h
    simpa only [Polynomial.derivative_map, Polynomial.eval₂_map,
      Polynomial.hom_eval₂, hcomp, hz₀, map_zero] using hh
  obtain ⟨b, hb, hred⟩ := localDivisionSubfield_hensel_lift K D ι
    (f.map φ) (hf.map _) z₀ hroot₀ hder₀
  refine ⟨b, ?_, by rw [hred]; exact hz₀⟩
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hb

end Embedded

/-- A residue minimal polynomial has a monic lift of exactly the same degree. -/
theorem exists_localDivision_residue_minpoly_polynomial
    (z : DivisionValuation.Residue (localReducedNormValuation K D)) :
    ∃ f : Polynomial 𝒪[K], f.Monic ∧
      f.map (IsLocalRing.residue 𝒪[K]) = minpoly 𝓀[K] z ∧
      f.natDegree = (minpoly 𝓀[K] z).natDegree ∧
      Irreducible (f.map (algebraMap 𝒪[K] K)) := by
  have hz : IsIntegral 𝓀[K] z := Algebra.IsIntegral.isIntegral z
  obtain ⟨f, hmap, hdeg, hmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective) (minpoly 𝓀[K] z))
    (minpoly.monic hz)
  refine ⟨f, hmon, hmap, hdeg, ?_⟩
  apply (hmon.irreducible_iff_irreducible_map_fraction_map (K := K)).mp
  exact Polynomial.Monic.irreducible_of_irreducible_map
    (IsLocalRing.residue 𝒪[K]) f hmon (hmap ▸ minpoly.irreducible hz)

/-- Every actual residue element has an integral lift with the same minimal-polynomial degree. -/
theorem exists_localDivision_residue_minpoly_lift
    (z : DivisionValuation.Residue (localReducedNormValuation K D)) :
    ∃ f : Polynomial 𝒪[K], ∃ b : (localReducedNormValuation K D).integer,
      f.Monic ∧ f.map (IsLocalRing.residue 𝒪[K]) = minpoly 𝓀[K] z ∧
      f.natDegree = (minpoly 𝓀[K] z).natDegree ∧
      f.map (algebraMap 𝒪[K] K) = minpoly K (b : D) ∧
      DivisionValuation.reduction _ b = z ∧ IsSeparable K (b : D) := by
  obtain ⟨a, ha⟩ := exists_residueGeneratorSubfield K D
  let := residueGeneratorField K D (a.val : D)
  let L := residueGeneratorSubalgebra K D (a.val : D)
  let ι : L →ₐ[K] D := (residueGeneratorSubalgebra K D (a.val : D)).val
  have hsurj : Function.Surjective (localDivisionSubfieldResidueMap K D ι) := ha
  obtain ⟨f, hmon, hmap, hdeg, hirr⟩ := exists_localDivision_residue_minpoly_polynomial K D z
  have heval (g : Polynomial 𝒪[K]) :
      Polynomial.aeval z (g.map (IsLocalRing.residue 𝒪[K])) =
        g.eval₂ (localDivisionBaseReduction K D) z := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hroot : f.eval₂ (localDivisionBaseReduction K D) z = 0 := by
    rw [← heval, hmap]
    exact minpoly.aeval 𝓀[K] z
  have hz : IsIntegral 𝓀[K] z := Algebra.IsIntegral.isIntegral z
  have hder : f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0 := by
    rw [← heval, ← Polynomial.derivative_map, hmap]
    exact (PerfectField.separable_of_irreducible (minpoly.irreducible hz)).aeval_derivative_ne_zero
      (minpoly.aeval 𝓀[K] z)
  obtain ⟨b, hb, hred⟩ := localDivisionSubfield_lift_base_polynomial K D ι
    hsurj f hmon z hroot hder
  let bD := localDivisionSubfieldIntegerMap K D ι b
  have hbD : Polynomial.aeval (bD : D) (f.map (algebraMap 𝒪[K] K)) = 0 := by
    let θ : (localDivisionSubfieldValuation K D ι).integer →+* D :=
      ι.toRingHom.comp (localDivisionSubfieldValuation K D ι).integer.subtype
    have hθ : θ.comp (localDivisionSubfieldBaseIntegerMap K D ι) =
        (algebraMap K D).comp (algebraMap 𝒪[K] K) := by
      ext x
      exact ι.commutes x.val
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hθ]
    change f.eval₂ (θ.comp (localDivisionSubfieldBaseIntegerMap K D ι)) (θ b) = 0
    rw [← Polynomial.hom_eval₂, hb, map_zero]
  have hmin : f.map (algebraMap 𝒪[K] K) = minpoly K (bD : D) :=
    minpoly.eq_of_irreducible_of_monic hirr hbD (hmon.map _)
  have hsep : (f.map (algebraMap 𝒪[K] K)).Separable := by
    apply (Polynomial.separable_iff_derivative_ne_zero hirr).mpr
    intro h
    have hd : f.derivative = 0 :=
      (Polynomial.map_eq_zero_iff (IsFractionRing.injective 𝒪[K] K)).mp
        (by simpa only [Polynomial.derivative_map] using h)
    exact hder (by rw [hd, Polynomial.eval₂_zero])
  refine ⟨f, bD, hmon, hmap, hdeg, hmin, hred, ?_⟩
  change (minpoly K (bD : D)).Separable
  rw [← hmin]
  exact hsep

/-- The degree comparison and separability concern an original integral element. -/
theorem exists_localDivision_residue_degree_lift
    (z : DivisionValuation.Residue (localReducedNormValuation K D)) :
    ∃ b : (localReducedNormValuation K D).integer,
      DivisionValuation.reduction _ b = z ∧ IsSeparable K (b : D) ∧
        (minpoly K (b : D)).natDegree = (minpoly 𝓀[K] z).natDegree := by
  obtain ⟨f, b, hmon, _, hdeg, hmin, hred, hsep⟩ :=
    exists_localDivision_residue_minpoly_lift K D z
  refine ⟨b, hred, hsep, ?_⟩
  rw [← hmin, hmon.natDegree_map, hdeg]

end Langlands.CentralDivision
