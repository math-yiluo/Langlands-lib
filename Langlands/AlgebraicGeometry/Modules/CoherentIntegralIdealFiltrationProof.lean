import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Quasicoherent

/-! # Proof of the coherent integral-ideal filtration statement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

/-- Every nonzero quasi-coherent module on a noetherian scheme contains the pushforward of a
nonzero coherent ideal sheaf on an integral closed subscheme. -/
theorem exists_mono_idealPushforward {X : Scheme.{u}} [IsNoetherian X] (Q : X.Modules)
    (hQ : Q.IsQuasicoherent) (hQ0 : ¬ IsZero Q) :
    ∃ (C : X.Modules) (φ : C ⟶ Q), Mono φ ∧ IsIdealPushforward C ∧ C.IsQuasicoherent ∧
      HasFiniteAffineSections C ∧ ¬ IsZero C := by
  obtain ⟨w⟩ := nonempty_witness hQ0
  have := w.isQuasicoherent_I
  refine ⟨_, w.phi, inferInstance,
    ⟨w.Z, w.i, inferInstance, inferInstance, w.I, w.ι, inferInstance, w.isQuasicoherent_I,
      w.hasFiniteAffineSections_I, w.not_isZero_I, ⟨Iso.refl _⟩⟩,
    QuasicoherentLocal.isQuasicoherent_pushforward w.i w.I,
    w.hasFiniteAffineSections_pushforward, w.not_isZero_pushforward⟩

end IntegralIdealFiltration

/-- Every quasi-coherent module with finite affine sections on a noetherian scheme has a finite
filtration whose successive quotients are pushforwards of nonzero coherent ideal sheaves on
integral closed subschemes. -/
theorem coherentIntegralIdealFiltration : CoherentIntegralIdealFiltrationStatement.{u} := by
  intro X _ M hM hMf
  have := hM
  exact (IntegralIdealFiltration.filtered_of_core
    (fun Q hQ _ hQ0 => IntegralIdealFiltration.exists_mono_idealPushforward Q hQ hQ0)
    M hMf).exists_chain

end Langlands.AlgebraicGeometry.Modules
