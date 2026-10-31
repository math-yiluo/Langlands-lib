import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawStatement
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper

/-! # Proof of the noetherian seesaw for line bundles on a flat proper family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A locally free rank-one sheaf is invertible in the sense of the ported FLT predicate:
restriction along an open immersion is isomorphic to pullback along it. -/
lemma isInvertible_of_isLocallyFreeRankOne {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) : Scheme.Modules.IsInvertible M :=
  ⟨fun x => by
    obtain ⟨U, hx, ⟨e⟩⟩ := hM x
    exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e⟩⟩⟩

/-- The noetherian seesaw for line bundles, deduced from the ported FLT theorem. -/
theorem noetherianLineBundleSeesaw : NoetherianLineBundleSeesawStatement.{u} := by
  intro R _ X c _ _ _ hH0 T _ t M M' hM hM'
  obtain ⟨Z, ι, hι, h⟩ :=
    Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
      c hH0 t M M' (isInvertible_of_isLocallyFreeRankOne hM)
      (isInvertible_of_isLocallyFreeRankOne hM')
  refine ⟨Z, ι, hι, fun {T'} ψ => ?_⟩
  rw [h ψ]
  unfold Scheme.Modules.LocallyIsoOver
  refine forall_congr' fun τ => exists_congr fun U => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨e⟩
    exact ⟨(Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫ e ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm⟩
  · rintro ⟨e⟩
    exact ⟨((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm ≪≫ e ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback _).app _⟩

end Langlands.AlgebraicGeometry.Picard
