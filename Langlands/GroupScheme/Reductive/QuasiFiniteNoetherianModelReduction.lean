import Langlands.GroupScheme.Descent.FiniteCoefficientQuasiFiniteModel

/-! # Noetherian models from finite coefficient homomorphism descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open Descent.FiniteCoefficient

/-- A reductive finite coefficient model over a noetherian ring gives the
required model over an actual subring of the original ring. -/
def Descent.FiniteCoefficient.QuasiFiniteSmoothAffineHomModel.toNoetherian
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}
    (D : QuasiFiniteSmoothAffineHomModel R A f)
    (hG : IsReductive D.source) (hH : IsReductive D.target) :
    NoetherianQuasiFiniteModel f where
  coefficients := D.coefficients.toSubring
  noetherian := by
    have : Algebra.FiniteType R D.coefficients :=
      (Subalgebra.fg_iff_finiteType _).mp D.finite
    exact Algebra.FiniteType.isNoetherianRing R D.coefficients
  source := D.source
  target := D.target
  source_reductive := hG
  target_reductive := hH
  hom := D.hom
  quasiFinite := D.homProperty.1.1
  flat := D.homProperty.1.2
  surjective := D.homProperty.2
  sourceIso := D.sourceIso
  targetIso := D.targetIso
  recovery := D.comm.symm

/-- The two explicit descent premises imply the unchanged noetherian model
statement in the same universe as the original base ring. -/
theorem reductiveQuasiFiniteNoetherianModel_of_descent
    (hHom : HomGeneralStatement.{u}) (hLimit : DirectLimitReductiveStatement.{u}) :
    ReductiveQuasiFiniteNoetherianModelStatement.{u} := by
  intro A _ G H hG hH f hq hf hs
  let : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let := hG.isAffineHom
  let := hG.smooth
  let := hH.isAffineHom
  let := hH.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨D, -⟩ := exists_quasiFiniteSmoothAffineHomModel
    (R := ULift.{u} ℤ) hHom f ⟨⟨hq, hf⟩, hs⟩ ∅
  obtain ⟨E, -, hEG, hEH⟩ := D.exists_reductive_extension hLimit hG hH
  exact ⟨E.toNoetherian hEG hEH⟩

end Langlands.GroupScheme
