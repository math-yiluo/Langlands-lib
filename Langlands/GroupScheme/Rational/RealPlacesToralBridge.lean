import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesSurjectivity
import Langlands.GroupScheme.Rational.GaloisTwistedPointDensity
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # From quadratic covers to real places -/

noncomputable section

universe u

open Polynomial AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- A single finite separable refinement gives toral representatives at every real place. -/
theorem realPlacesToralRepresentatives :
    RealPlacesToralRepresentativesStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ c
  let E := (X ^ 2 + C (1 : L)).SplittingField
  let : FiniteDimensional F E := FiniteDimensional.trans F L E
  let : Algebra.IsSeparable F E := inferInstance
  let e : L →ₐ[F] E := IsScalarTower.toAlgHom F L E
  obtain ⟨i, hi⟩ := Langlands.FieldTheory.exists_sq_eq_neg_one_splittingField L
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, e, fun w => ?_⟩
  let K := w.1.Completion
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hGK := connectedReductiveFieldExtensionStatement F K G hG.isSemisimple.isConnectedReductive
  exact toralRepresentative_realBaseChange_of_quadratic quadraticToralRepresentatives F K E
    (InfinitePlace.Completion.ringEquivRealOfIsReal w.2) hi _ hGK ((c w).refine _)

end Langlands.GroupScheme
