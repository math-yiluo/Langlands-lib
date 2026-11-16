import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.FiniteEtaleUnder

/-! # Cancellation of finite Banach algebra maps -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [NormedAlgebra K R] [NormedAlgebra K S] [NormedAlgebra K T]

/-- A finite Banach composite is finite Banach over the intermediate algebra.
The first map needs only its given boundedness. -/
theorem IsFiniteBanach.of_comp {f : BoundedAlgHom K R S} {g : BoundedAlgHom K S T}
    (hgf : (g.comp f).IsFiniteBanach) : g.IsFiniteBanach := by
  obtain ⟨n, b, C, hC, hb⟩ := hgf
  obtain ⟨D, hD, hf⟩ := f.bounded
  refine ⟨n, b, D * C, mul_pos hD hC, fun y => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hb y
  refine ⟨fun i => f (c i), hc, ?_⟩
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg hD.le hC.le) (norm_nonneg y))).2 fun i => ?_
  calc
    ‖f (c i)‖ ≤ D * ‖c i‖ := hf _
    _ ≤ D * ‖c‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) hD.le
    _ ≤ D * (C * ‖y‖) := mul_le_mul_of_nonneg_left hcn hD.le
    _ = D * C * ‖y‖ := (mul_assoc _ _ _).symm

/-- Cancel an algebraically finite étale first map while retaining the
admissible finite Banach presentation of the composite. -/
theorem finiteBanach_etale_of_comp {f : BoundedAlgHom K R S}
    {g : BoundedAlgHom K S T} (hf : f.AlgebraicallyFiniteEtale)
    (hgf : (g.comp f).IsFiniteBanach ∧ (g.comp f).AlgebraicallyFiniteEtale) :
    g.IsFiniteBanach ∧ g.AlgebraicallyFiniteEtale :=
  ⟨hgf.1.of_comp, AlgebraicallyFiniteEtale.of_comp hf hgf.2⟩

end Langlands.Analytic.BoundedAlgHom
