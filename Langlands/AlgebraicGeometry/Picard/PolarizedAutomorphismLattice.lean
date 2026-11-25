import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphismRosati
import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphismFinitenessStatement
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityStatement
import Langlands.AlgebraicGeometry.Picard.RosatiRationalInverseStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityProof
import Langlands.LinearAlgebra.RationalPositiveLattice

/-! # Conditional lattice reduction for actual polarized automorphism finiteness -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Rosati

variable (P : Prerequisites.{u}) {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
  [HasRationalInverse P W lam]

local notation "AutLam" => AbelianScheme.polarizedAutGroup P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
  W.geometry W.inversePoincare W.evaluation lam

/-- Actual integral polarized automorphisms embed in the constant-trace ball
of the actual integral Rosati form. -/
def polarizedAutTraceBallEmbedding :
    AutLam ↪ Langlands.rationalBilinearBall (integralTraceForm P W hadd lam)
      (geometricEndomorphismTrace A 1) where
  toFun f := ⟨CategoryTheory.End.of f.val.asIso.hom,
    (polarizedAut_integralTraceForm_self P W hadd lam f).le⟩
  inj' f g h := by
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    exact congrArg CategoryTheory.End.asHom (congrArg Subtype.val h)

/-- Symmetry and strict positivity of the actual rational trace form imply
finiteness when the actual integral endomorphisms form a finite free lattice. -/
theorem finite_polarizedAutGroup_of_traceForm [CharZero k]
    [Module.Free ℤ (CategoryTheory.End A)] [Module.Finite ℤ (CategoryTheory.End A)]
    (hsym : ∀ a b : End0 A, traceForm P W hadd lam a b = traceForm P W hadd lam b a)
    (hpos : ∀ a : End0 A, a ≠ 0 → 0 < traceForm P W hadd lam a a) :
    Finite AutLam := by
  have hball := Langlands.finite_rational_bilinear_le (integralTraceForm P W hadd lam)
    (fun a b => hsym (endToEnd0 A a) (endToEnd0 A b))
    (fun a ha => hpos (endToEnd0 A a) (by
      intro h
      apply ha
      apply CategoryTheory.End.ext
      apply homToHom0_injective_of_charZero A A
      exact (congrArg CategoryTheory.End.asHom h).trans (map_zero homToHom0).symm))
    (geometricEndomorphismTrace A 1)
  have := hball.to_subtype
  exact Finite.of_injective (polarizedAutTraceBallEmbedding P W hadd lam)
    (polarizedAutTraceBallEmbedding P W hadd lam).injective

end Langlands.AbelianScheme.Rosati

namespace Langlands.AbelianScheme

open Rosati

/-- The exact existing finiteness target follows from the actual geometric
Rosati inverse and positivity targets and finite freeness of actual integral End.
All three mathematical obligations remain explicit premises. -/
theorem polarizedAutomorphismFiniteness_of_rosati_and_lattice
    (inverse : RationalInverseStatement.{u})
    (positivity : PositivityStatement.{u})
    (lattice : ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
      (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))),
      Module.Free ℤ (CategoryTheory.End A) ∧ Module.Finite ℤ (CategoryTheory.End A)) :
    PolarizedAutomorphismFinitenessStatement.{u} := by
  intro preservation square universality composition unitCoherence associativity
    comparison symmetry stability k _ _ _ A hA geometryA MA evaluationA lam hlam
  let P : Prerequisites.{u} :=
    ⟨preservation, composition, unitCoherence, associativity, comparison, symmetry,
      stability, square, universality⟩
  let W : DualData A := ⟨hA, geometryA, MA, evaluationA⟩
  have hlam' : W.IsPolarization P lam := hlam
  let : HasRationalInverse P W lam := inverse P k A W lam hlam'
  let : Module.Free ℤ (CategoryTheory.End A) := (lattice k A).1
  let : Module.Finite ℤ (CategoryTheory.End A) := (lattice k A).2
  let hadd : W.Additivity P :=
    fieldDualSchemeMapAdditivity P.preservation P.stability k A A W.hasDual W.hasDual
  have hp := positivity P k A W hadd lam hlam'
  exact finite_polarizedAutGroup_of_traceForm P W hadd lam hp.1 hp.2.2

end Langlands.AbelianScheme
