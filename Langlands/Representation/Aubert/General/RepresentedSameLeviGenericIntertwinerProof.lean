import Langlands.Representation.Aubert.General.RepresentedSameLeviGenericIntertwinerStatement
import Langlands.Representation.Aubert.General.RepresentedSameLeviGenericRegularity
import Langlands.Representation.Aubert.General.RepresentedSameLeviRegularIntertwiner

/-! # Generic nonzero morphisms between represented inductions sharing a Levi -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Generic nonzero morphisms `i_P^G(σψ) → i_Q^G(σψ)` for represented parabolics with the
same Levi subgroup (Renard VII.3): off the zero locus of a nonzero polynomial the twist is
`PQ`-regular, and `PQ`-regularity produces a nonzero morphism. -/
theorem representedSameLeviGenericNonzeroIntertwiner :
    RepresentedSameLeviGenericNonzeroIntertwinerStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame
  let := leviPointTopology l hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ hirr hadm
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨poly, hpoly, hreg⟩ := exists_generic_isPQRegular k G hG P M N Q U
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha σ hirr hadm
  refine ⟨poly, hpoly, fun ψ hψ => ?_⟩
  have hτ := (SmoothRep.isIrreducible_twist_iff ψ.val.toMonoidHom
    (Plancherel.unramifiedCharacter_isOpen_ker _ ψ) σ).mpr hirr
  have : Nontrivial (σ.twist ψ.val.toMonoidHom
      (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)) := by
    have := hτ
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M))
      (σ.twist ψ.val.toMonoidHom
        (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)).representation.asModule
  exact exists_ne_zero_of_isPQRegular k G hG P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ
    hmulQ hsame A a ha _ this (hreg ψ hψ)

end Langlands.Aubert.General.RepresentedParabolic
