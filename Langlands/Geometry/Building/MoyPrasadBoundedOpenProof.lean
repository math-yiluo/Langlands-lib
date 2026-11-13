import Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement
import Langlands.Geometry.Building.MoyPrasadTopology

/-!
# Proof of `MoyPrasadBoundedOpenStatement` (KP Proposition 13.2.5, opening sentence)

Every Moy–Prasad subgroup `P_{x,r}` of supplied building data, at a point `x` of the
apartment and a finite depth `r ≥ 0`, is open and algebraically bounded in `G(F)` with the
canonical rational-point topology.
-/

universe u

namespace Langlands.Geometry.Building

/-- **KP Proposition 13.2.5, opening sentence, at finite depths, on supplied data.** For
apartment axioms `hP` and a supplied filtration of `Z(F)` whose depth subgroups are open
(`hZo`), each `P_{x,r}` is open (KP Corollary 8.2.6 with V 7) and algebraically bounded
(inside the norm-one fixer of `x`, bounded by KP Corollary 7.3.14). The four algebraic
filtration axioms are not used. -/
theorem moyPrasadBoundedOpen : MoyPrasadBoundedOpenStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP _ hZo x r
  exact ⟨Zf.isOpen_moyPrasad hP.topologyCompatible hZo x r,
    Zf.isAlgebraicallyBounded_moyPrasad hP x r⟩

end Langlands.Geometry.Building
