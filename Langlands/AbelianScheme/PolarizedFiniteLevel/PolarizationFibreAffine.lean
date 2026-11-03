import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenStatement
import Langlands.AbelianScheme.OrderSaturationExistence
import Mathlib.AlgebraicGeometry.Fiber

/-! # Affine fibre neighbourhoods from the fixed polarization bundle -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u})

/-- A polarization on any actual dual presentation makes its fixed diagonal bundle ample
over the original field, without dimension, degree or level data. -/
theorem DualWitness.diagonalBundle_isAmple_overField
    {K : Type u} [Field K] {A : AbelianScheme (Spec (.of K))}
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam) :
    (poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)).IsAmple := by
  let F := AlgebraicClosure K
  let b : Spec (.of F) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K F))
  have hf := hlam.2 F b
  have ham := poincareDiagonal_isAmple_of_fieldPresentation P F
    ((baseChange b).obj A) (W.pullback P b)
    (dualBaseChangeMap A W.hasDual P.universality b (W.parameterMap P lam)) hf
  have hbase : ((LineBundle.pullback
      (CategoryTheory.Limits.pullback.fst A.X.hom b)).obj
        (poincareDiagonalBundle A W.hasDual (W.parameterMap P lam))).IsAmple :=
    ham.of_iso ((LineBundle.forget _).mapIso
      (poincareDiagonalBaseChangeIso P.universality b A W.hasDual (W.parameterMap P lam)))
  exact fieldBaseChangeAmpleReflection K F b A.X.left A.X.hom
    (poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)) hbase

variable {S : Scheme.{u}} {A : AbelianScheme S}

/-- The actual pullback of the fixed diagonal bundle is ample on every residue-field fibre,
including fibres at nonclosed points. -/
theorem DualWitness.diagonalBundle_isAmple_onFibre
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam) (s : S) :
    ((LineBundle.pullback (A.X.hom.fiberι s)).obj
      (poincareDiagonalBundle A W.hasDual (W.parameterMap P lam))).IsAmple := by
  let b := S.fromSpecResidueField s
  let W' := W.pullback P b
  let lam' := W.pullbackMap P b W' lam
  have hlam' : W'.IsPolarization P lam' :=
    P.polarizationBaseChange P.preservation P.square P.universality P.stability
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.compatibility
      S (Spec (.of (S.residueField s))) b A W.hasDual W.geometry W.inverseBundle W.evaluation
      W'.hasDual W'.geometry W'.inverseBundle W'.evaluation lam hlam
  have ham := W'.diagonalBundle_isAmple_overField P lam' hlam'
  change (poincareDiagonalBundle ((baseChange b).obj A) W'.hasDual
    (W'.parameterMap P (W.pullbackMap P b W' lam))).IsAmple at ham
  rw [DualWitness.parameterMap_pullbackMap] at ham
  exact ham.of_iso ((LineBundle.forget _).mapIso
    (poincareDiagonalBaseChangeIso P.universality b A W.hasDual (W.parameterMap P lam)))

/-- The generic proper-family fibre-ampleness result supplies the finite-set affine criterion
for any actual polarized abelian scheme over a locally noetherian base. -/
theorem DualWitness.forall_finset_fibre_affine
    (fibreAmple : ProperFibreAmpleAffineOpenStatement.{u}) [IsLocallyNoetherian S]
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam) :
    ∀ (E : Finset A.X.left) (s : S), (∀ x ∈ E, A.X.hom x = s) →
      ∃ V : A.X.left.Opens, IsAffineOpen V ∧ ∀ x ∈ E, x ∈ V := by
  intro E s hE
  exact fibreAmple A.X.left S A.X.hom
    (poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)) s
    (W.diagonalBundle_isAmple_onFibre P lam hlam s) E hE

/-- Quotient existence follows from the fixed polarization bundle and the generic
proper-family fibre-ampleness theorem. -/
theorem DualWitness.nonempty_quotientData
    (fibreAmple : ProperFibreAmpleAffineOpenStatement.{u}) [IsLocallyNoetherian S]
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam)
    (K : FiniteEtaleSubgroup A) : Nonempty K.QuotientData :=
  FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre A
    (W.forall_finset_fibre_affine P fibreAmple lam hlam) K

/-- Construct the actual integral order model from a supplied polarization once the
generic fibre-ampleness theorem is available. -/
def DualWitness.integralOrderModel
    (fibreAmple : ProperFibreAmpleAffineOpenStatement.{u}) [IsLocallyNoetherian S]
    (W : DualWitness A) (lam : A ⟶ W.dual P) (hlam : W.IsPolarization P lam)
    (htor : TorsionFiniteEtaleStatement.{u})
    {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))
    {O : Type v} [Ring O] {I : Type u} [Fintype I] (b : Module.Basis I ℤ O)
    (α : O →+* Rationalization.End A) : IntegralOrderModel α :=
  integralOrderModelOfForallFinsetFibre htor p b α
    (W.forall_finset_fibre_affine P fibreAmple lam hlam)

end Langlands.AbelianScheme.PolarizedFiniteLevel
