import Langlands.AlgebraicGeometry.Modules.IntegralAmpleEulerCoefficientStatement
import Langlands.AlgebraicGeometry.Modules.IntegralSupportDimensionProof
import Langlands.AlgebraicGeometry.Picard.SectionCokernelEulerCoefficientProof

/-! # Positive integral ample coefficient from an actual coherent cut -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The lower-dimensional coherent coefficient criterion detects the
exact-dimensional ample section cokernel and forces the next coefficient
of the structure-module polynomial to be positive. -/
theorem integral_lineBundleEulerPolynomial_coeff_pos :
    IntegralAmpleEulerCoefficientStatement.{u} := by
  intro d ih K _ X _ _ _ f _ L hL hdim
  obtain ⟨n, hn, s, hs, hQc, hQ, hQdim⟩ :=
    exists_ampleSection_coherent_cokernel_dimension X L hL d hdim
  let Q := cokernel (sectionHom (tensorPow L.obj n) s)
  let : Q.IsQuasicoherent := hQc
  have hQbound : HasSupportDimensionLT Q (d + 1) := by
    apply (hasSupportDimensionLT_iff_supportDimension Q (d + 1)).mpr
    rw [hQdim]
    exact_mod_cast Nat.lt_succ_self d
  have hQnot : ¬ HasSupportDimensionLT Q d := by
    intro h
    have hlt := (hasSupportDimensionLT_iff_supportDimension Q d).mp h
    rw [hQdim] at hlt
    exact lt_irrefl _ hlt
  have hpos := (ih K X f Q hQ L hL hQbound).2.mpr hQnot
  have heq := Picard.sectionCokernelEulerCoefficient K X f d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le) L n s hs hQ hQbound
  rw [heq] at hpos
  have hscalar : (0 : ℚ) < ((d + 1 : ℕ) : ℚ) * (n : ℚ) :=
    mul_pos (by exact_mod_cast Nat.succ_pos d) (by exact_mod_cast hn)
  exact (mul_pos_iff_of_pos_left hscalar).mp hpos

end Langlands.AlgebraicGeometry.Modules.DerivedSections
