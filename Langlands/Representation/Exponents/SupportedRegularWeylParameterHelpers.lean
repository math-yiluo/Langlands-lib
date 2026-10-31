import Langlands.Representation.Classification.UnitaryWeylRigidityProof
import Langlands.Representation.Exponents.RealTwistFamilies
import Langlands.Representation.Exponents.SupportedRegularWeylParameterCones

/-! Local adapters for the supported regular Weyl comparison proof. -/

noncomputable section

namespace Langlands.SupportedRegularWeylComparison

open GeneralLinear Geometric

universe uF uV uW

/-- The coordinate equality supplied by real-exponent rigidity gives the
fixed relation with the same permutation and target-coordinate convention. -/
theorem fixedRelation_of_nestedParameter_eq {n : ℕ}
    (B1 B2 : BlockShape n) (S1 : BlockRefinement B1) (S2 : BlockRefinement B2)
    (v1 : Fin (B1.flatten S1).length → ℝ) (t1 : Fin B1.length → ℝ)
    (v2 : Fin (B2.flatten S2).length → ℝ) (t2 : Fin B2.length → ℝ)
    (w : Equiv.Perm (Fin n))
    (h : ∀ a : Fin n,
      RealTwistFamilies.nestedParameter B2 S2 v2 t2 (blockIndex (B2.flatten S2) (w a)) =
        RealTwistFamilies.nestedParameter B1 S1 v1 t1 (blockIndex (B1.flatten S1) a)) :
    ∀ a : Fin n,
      v1 (blockIndex (B1.flatten S1) (w.symm a)) - t1 (blockIndex B1 (w.symm a)) =
        v2 (blockIndex (B2.flatten S2) a) - t2 (blockIndex B2 a) := by
  intro a
  have ha := h (w.symm a)
  simp only [Equiv.apply_symm_apply, RealTwistFamilies.nestedParameter_apply,
    UnitaryWeylRigidity.flattenBlockEquiv_symm_blockIndex] at ha
  linarith

/-- Apply the existing unitary exponent rigidity to actual nested fine twists. -/
theorem fixedRelation_of_twistedEquiv
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ}
    (B1 B2 : BlockShape n) (S1 : BlockRefinement B1) (S2 : BlockRefinement B2)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ω1 : Representation ℂ ((B1.flatten S1).Levi F.Carrier) V)
    (ω2 : Representation ℂ ((B2.flatten S2).Levi F.Carrier) W)
    (hω1i : Representation.IsIrreducible ω1)
    (hω1c : letI := T.topology
      CuspidalSupport.IsLeviCuspidal (B1.flatten S1) ω1)
    (hω1u : IsUnitarizable ω1)
    (hω2i : Representation.IsIrreducible ω2)
    (hω2c : letI := T.topology
      CuspidalSupport.IsLeviCuspidal (B2.flatten S2) ω2)
    (hω2u : IsUnitarizable ω2)
    (v1 : Fin (B1.flatten S1).length → ℝ) (t1 : Fin B1.length → ℝ)
    (v2 : Fin (B2.flatten S2).length → ℝ) (t2 : Fin B2.length → ℝ)
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi
      (F := F.Carrier) (B1.flatten S1) (B2.flatten S2) w)
    (he : Nonempty ((CuspidalSupport.transport (F := F.Carrier)
        (B1.flatten S1) (B2.flatten S2) w hw
        (T.leviRealPowerTwist (B1.flatten S1)
          (RealTwistFamilies.nestedParameter B1 S1 v1 t1) ω1)).Equiv
        (T.leviRealPowerTwist (B2.flatten S2)
          (RealTwistFamilies.nestedParameter B2 S2 v2 t2) ω2))) :
    ∀ a : Fin n,
      v1 (blockIndex (B1.flatten S1) (w.symm a)) - t1 (blockIndex B1 (w.symm a)) =
        v2 (blockIndex (B2.flatten S2) a) - t2 (blockIndex B2 a) := by
  let := T.topology
  obtain ⟨e⟩ := he
  apply fixedRelation_of_nestedParameter_eq B1 B2 S1 S2 v1 t1 v2 t2 w
  exact UnitaryWeylRigidity.coordinate_exponent_eq T
    hω1i hω1c.1 hω1u hω2i hω2c.1 hω2u hw e

end Langlands.SupportedRegularWeylComparison
