import Langlands.Global.Factors.CuspidalInducedConstituentAutomorphyStatement
import Langlands.Global.Factors.CuspidalIsobaricFiniteFamily
import Langlands.Global.Factors.CuspidalIsobaricRealizationStatement

/-! The implication from automorphy of cuspidally induced constituents to
finite-place automorphic realization of cuspidal isobaric sums. -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

/-- The finite-place constituent automorphy theorem implies the finite-place
isobaric realization theorem. -/
def CuspidalIsobaricRealizationReductionStatement : Prop :=
  CuspidalInducedConstituentAutomorphyStatement.{u, uQ} →
    CuspidalIsobaricRealizationStatement.{u, uQ}

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- Apply constituent automorphy to the family of finite-place isobaric sums
and its common spherical exception set. -/
theorem cuspidalIsobaricRealizationReduction :
    CuspidalIsobaricRealizationReductionStatement.{u, uQ} := by
  intro hautomorphy F _ _ _ r k m hm T P h
  obtain ⟨A, S, hsum, hind, hsph⟩ := cuspidalIsobaricFiniteFamily F r k m hm T P h
  obtain ⟨Q, hemb⟩ := hautomorphy F r k m hm T P h A S hind hsph
  exact ⟨Q, fun v => ⟨A v, hsum v, hind v, hemb v⟩⟩

end Langlands.Global
