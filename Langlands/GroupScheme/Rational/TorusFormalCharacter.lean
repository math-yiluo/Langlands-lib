import Langlands.GroupScheme.Rational.TorusClassFunctionRestriction
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition

/-! # Formal characters of actual representations on a split maximal torus -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The affine base-field test of a composite rational point is the composite. -/
theorem rationalAffinePoint_comp (g : rationalPoints H) (f : H ⟶ G) :
    rationalAffinePoint (g ≫ f.hom.hom) = rationalAffinePoint g ≫ f.hom.hom :=
  (Category.assoc _ _ _).symm

/-- On the affine base-field test of a rational point, the affine `𝔾_m` identification
returns the rational character value. -/
theorem affineUnitsEquiv_rationalAffinePoint (χ : rationalCharacters H)
    (g : rationalPoints H) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) k)
        (rationalAffinePoint g ≫ χ.toMul.hom.hom) =
      rationalCharacterEval χ g := by
  rw [rationalCharacterEval_eq_affineUnitsEquiv H χ g, GroupScheme.affinePointsTarget_apply]
  congr 2

end MatrixRepresentation

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- At the affine base-field test of a rational torus point, the character value used by
`SplitCharacterPoint.pointLift` is the rational character value. -/
theorem value_rationalAffinePoint (wt : characterLattice p.torus)
    (s : rationalPoints p.torus.toGrp) :
    (SplitCharacterPoint.value wt (MatrixRepresentation.rationalAffinePoint s) : k) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm wt) s :
        k) :=
  congrArg Units.val (MatrixRepresentation.affineUnitsEquiv_rationalAffinePoint
    ((rationalCharacters.equivCharacterLattice p.torus).symm wt) s)

/-- Evaluating an element of the group algebra of the character lattice at a rational torus
point sums its coefficients against the rational character values. -/
theorem pointLift_rationalAffinePoint (x : AddMonoidAlgebra k (characterLattice p.torus))
    (s : rationalPoints p.torus.toGrp) :
    SplitCharacterPoint.pointLift (MatrixRepresentation.rationalAffinePoint s) x =
      x.coeff.sum (fun wt a => a *
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm wt)
          s : k)) := by
  rw [SplitCharacterPoint.pointLift, AddMonoidAlgebra.lift_apply']
  refine Finsupp.sum_congr fun wt _ => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    SplitCharacterPoint.valueHom_apply, toAdd_ofAdd, Algebra.algebraMap_self, RingHom.id_apply]
  rw [p.value_rationalAffinePoint wt s]

/-- Two rational points of the split torus with the same image in the class-function quotient
give the same value of the torus restriction of every class function. -/
theorem pointLift_torusRestriction_eq_of_rho_eq (s t : rationalPoints p.torus.toGrp)
    (h : (s ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G =
      (t ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G) (f : ClassFunctions.algebra G) :
    SplitCharacterPoint.pointLift (MatrixRepresentation.rationalAffinePoint s)
        (p.torusRestriction f) =
      SplitCharacterPoint.pointLift (MatrixRepresentation.rationalAffinePoint t)
        (p.torusRestriction f) := by
  rw [← p.pointCoordinates_torusPoint, ← p.pointCoordinates_torusPoint]
  apply ClassFunctions.evaluation_eq_of_rho_eq
  simp only [MatrixRepresentation.rationalAffinePoint, Category.assoc] at h ⊢
  rw [h]

variable {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- The formal character of an actual representation on the supplied split maximal torus:
the coefficient function of the torus restriction of its trace class function. Its value at
a weight is the dimension of the weight space (`formalCharacter_apply`). -/
def formalCharacter : characterLattice p.torus →₀ k :=
  (p.torusRestriction (MatrixRepresentation.traceClassFunction ρ)).coeff

/-- The coefficients of the formal character are the weight multiplicities, as elements of
the base field. -/
theorem formalCharacter_apply (wt : characterLattice p.torus) :
    p.formalCharacter ρ wt = (Module.finrank k (p.representationWeightSpace ρ wt) : k) :=
  p.torusRestriction_traceClassFunction_coeff ρ (p.iSup_representationWeightSpace_eq_top ρ) wt

/-- Every root reflection preserves the formal character. -/
theorem formalCharacter_reflection (α : p.rootIndex) (wt : characterLattice p.torus) :
    p.formalCharacter ρ (p.rootDatum.reflection α wt) = p.formalCharacter ρ wt :=
  p.torusRestriction_coeff_reflection _ α wt

/-- A weight with nonzero formal-character coefficient has a nonzero weight space. -/
theorem representationWeightSpace_ne_bot_of_formalCharacter_ne_zero
    {wt : characterLattice p.torus} (hwt : p.formalCharacter ρ wt ≠ 0) :
    p.representationWeightSpace ρ wt ≠ ⊥ := by
  intro hbot
  apply hwt
  rw [formalCharacter_apply, hbot, finrank_bot, Nat.cast_zero]

/-- The trace of a rational torus point is the formal character summed against the values
of the weights at that point. -/
theorem formalCharacter_sum_eq_trace (s : rationalPoints p.torus.toGrp) :
    (p.formalCharacter ρ).sum (fun wt a => a *
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm wt)
          s : k)) =
      Matrix.trace (ρ.rationalMatrix (s ≫ p.inclusion.hom.hom) : Matrix n n k) := by
  rw [formalCharacter, ← p.pointLift_rationalAffinePoint, ← p.pointCoordinates_torusPoint,
    MatrixRepresentation.traceClassFunction_evaluate,
    MatrixRepresentation.rationalMatrix_eq_affineMatrix,
    MatrixRepresentation.rationalAffinePoint_comp]

/-- **Highest-weight character data.** For a highest-weight representation of weight `lam`
and two rational points of the split torus with the same image in the class-function
quotient, the formal character is a finitely supported function on the character lattice
that is invariant under every root reflection, equals `1` at `lam`, is supported below `lam`
in dominance order, and has the same sum against the character values at both points. -/
theorem exists_invariant_triangular_of_rho_eq (lam : characterLattice p.torus)
    (hρ : p.IsHighestWeight ρ lam) (s t : rationalPoints p.torus.toGrp)
    (h : (s ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G =
      (t ≫ p.inclusion.hom.hom) ≫ ClassFunctions.rho G) :
    ∃ c : characterLattice p.torus →₀ k,
      (∀ (α : p.rootIndex) (wt : characterLattice p.torus),
        c (p.rootDatum.reflection α wt) = c wt) ∧
      c lam = 1 ∧
      (∀ wt, c wt ≠ 0 → lam - wt ∈ p.positiveRootMonoid) ∧
      c.sum (fun wt a => a *
          (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm wt)
            s : k)) =
        c.sum (fun wt a => a *
          (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm wt)
            t : k)) := by
  refine ⟨p.formalCharacter ρ, p.formalCharacter_reflection ρ, ?_, ?_, ?_⟩
  · rw [formalCharacter_apply, hρ.2.2.1, Nat.cast_one]
  · intro wt hwt
    exact hρ.2.2.2 wt (p.representationWeightSpace_ne_bot_of_formalCharacter_ne_zero ρ hwt)
  · rw [formalCharacter, ← p.pointLift_rationalAffinePoint, ← p.pointLift_rationalAffinePoint]
    exact p.pointLift_torusRestriction_eq_of_rho_eq s t h _

end SplitPinning

end Langlands.GroupScheme
