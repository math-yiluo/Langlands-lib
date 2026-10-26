import Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraStatements
import Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraProof
import Mathlib.RingTheory.Etale.Pi

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable (R A G : Type u)
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]

omit [IsNoetherianRing R] [Module.Finite R A] [Algebra.Etale R A] [Finite G] in
private theorem fixedPoints_eq_equalizer :
    FixedPoints.subalgebra R A G =
      AlgHom.equalizer (AlgHom.pi (fun g : G => MulSemiringAction.toAlgHom R A g))
        (AlgHom.pi (fun _ : G => AlgHom.id R A)) := by
  ext a
  change (∀ g : G, g • a = a) ↔ (fun g : G => g • a) = (fun _ : G => a)
  exact funext_iff.symm

/-- The invariant subalgebra of a finite étale algebra under a finite group
action is finite and étale over the noetherian base. -/
theorem invariantAlgebraFiniteEtale :
    InvariantAlgebraFiniteEtale R A G := by
  let f : A →ₐ[R] (G → A) := AlgHom.pi (fun g => MulSemiringAction.toAlgHom R A g)
  let g : A →ₐ[R] (G → A) := AlgHom.pi (fun _ => AlgHom.id R A)
  have h : Algebra.Etale R (AlgHom.equalizer f g) :=
    (equalizerAlgebraFiniteEtale R A (G → A) f g).2
  have heq : FixedPoints.subalgebra R A G = AlgHom.equalizer f g :=
    fixedPoints_eq_equalizer R A G
  constructor
  · exact Module.Finite.of_injective
      (FixedPoints.subalgebra R A G).val.toLinearMap Subtype.val_injective
  · rw [heq]
    exact h

end Langlands.AlgebraicGeometry.FiniteEtale
