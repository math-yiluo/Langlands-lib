import Langlands.Representation.Hecke.Intertwiner

/-! # Transfer original-map equalities to integrated Hecke intertwiners -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure

universe uG uV uW uP

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {P : Type uP} [AddCommGroup P] [Module ℂ P]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
variable {τ : Representation ℂ G P}

/-- An original identity law passes to the unchanged integrated map. -/
theorem heckeActionIntertwiner_id_of_eq (hρ : IsSmooth ρ)
    (T : ρ.IntertwiningMap ρ) (hT : T = Representation.IntertwiningMap.id ρ) :
    heckeActionIntertwiner μ hρ hρ T =
      Algebra.LinearIntertwiner.id (heckeAction μ ρ hρ) := by
  subst T
  exact heckeActionIntertwiner_id μ hρ

/-- An original composition law passes to the unchanged integrated maps. -/
theorem heckeActionIntertwiner_comp_of_eq (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hτ : IsSmooth τ) (T : ρ.IntertwiningMap σ) (U : σ.IntertwiningMap τ)
    (TU : ρ.IntertwiningMap τ) (hTU : TU = U.comp T) :
    heckeActionIntertwiner μ hρ hτ TU =
      (heckeActionIntertwiner μ hσ hτ U).comp (heckeActionIntertwiner μ hρ hσ T) := by
  subst TU
  exact heckeActionIntertwiner_comp μ hρ hσ hτ T U

end Langlands.Hecke
