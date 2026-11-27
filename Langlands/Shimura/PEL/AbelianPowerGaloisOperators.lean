import Langlands.AbelianScheme.RelativePower
import Langlands.AbelianScheme.Rational
import Langlands.CategoryTheory.RationalizationDenominators
import Langlands.Cohomology.HodgeTate.ProperSmoothStatement
import Langlands.Shimura.PEL.CohomologicalProjectorPolynomial
import Mathlib.Algebra.FreeAlgebra

/-! # Geometric cohomology operators on powers of a PEL abelian scheme -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry EtaleGaloisAction EtaleDerivedSections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe wS wR

namespace Langlands.Cohomology.AbelianPower

open Langlands.AbelianScheme Langlands.Shimura.PEL.CohomologicalProjector

variable {S : Scheme.{0}} (B : Langlands.AbelianScheme S)
variable {F : Type} [Field F] (s : S ⟶ Spec (CommRingCat.of F))
variable (m : ℕ)

/-- The abelian power as a scheme over the ground field. -/
abbrev overField : Over (Spec (CommRingCat.of F)) :=
  (Over.map s).obj (relativePower B m)

private abbrev f := (overField B s m).hom

variable (p : ℕ) [Fact p.Prime]
variable {Λ : Type} [Field Λ] (j : ℚ_[p] →+* Λ)
variable [HasDerivedCategory.{wS} (ModuleSheaf (baseChange F (AlgebraicClosure F) (f B s m)) ℤ_[p])]
variable [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])]

/-- The actual geometric cohomology with its Galois action, extended
from `ℚ_p` to the specified coefficient field. -/
def cohomologyAction (q : ℕ) : Action (ModuleCat Λ) (Field.absoluteGaloisGroup F) :=
  ((ModuleCat.extendScalars j).mapAction _).obj
    (HodgeTate.ellAdicEtaleAction (f B s m) p q)

/-- The cohomology pullback of an actual endomorphism of the power over `S`. -/
def geometricPullback (b : relativePower B m ⟶ relativePower B m) (q : ℕ) :
    Module.End Λ (cohomologyAction B s m p j q).V :=
  ((ModuleCat.extendScalars j).map
    (HodgeTate.ellAdicEtalePullback p ((Over.map s).map b) q)).hom

/-- The polynomial in the actual multiplication-by-two pullbacks. -/
def degreeOneSelector (d q : ℕ) : Module.End Λ (cohomologyAction B s m p j q).V :=
  degreeOneEndomorphism Λ d fun i =>
    geometricPullback B s m p j (relativePowerDouble B m i) q

variable {D : Type} [Ring D] (ι : D →+* End0 B)

/-- A rationalized endomorphism represented by an actual integral map
with a nonzero denominator. -/
structure IntegralMultiple (b : End0 B) where
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  hom : B ⟶ B
  rationalization_eq : homToHom0 hom = denominator • b.asHom

/-- Clear denominators on the actual abelian-scheme Hom group. -/
def integralMultiple (b : End0 B) : IntegralMultiple B b :=
  let existsLift := Langlands.Rationalization.exists_integral_multiple b.asHom
  ⟨existsLift.choose, existsLift.choose_spec.1,
    existsLift.choose_spec.2.choose, existsLift.choose_spec.2.choose_spec⟩

/-- A PEL-algebra element on a specified factor, or a factor permutation. -/
abbrev GeometricOperator (D : Type) (m : ℕ) := (Fin m × D) ⊕ Equiv.Perm (Fin m)

/-- Apply the supplied integral endomorphism to one factor of the power. -/
def factorMap (i : Fin m) (a : B ⟶ B) : relativePower B m ⟶ relativePower B m :=
  relativePowerLift B m fun k =>
    relativePowerProjection B m k ≫ if k = i then (groupHom a).hom.hom else 𝟙 _

/-- Evaluate a generator as the pullback of an actual map of the abelian power. -/
def generator (q : ℕ) : GeometricOperator D m →
    Module.End Λ (cohomologyAction B s m p j q).V
  | .inl ⟨i, a⟩ =>
      let b := integralMultiple B (ι a)
      ((b.denominator : Λ)⁻¹) • geometricPullback B s m p j (factorMap B m i b.hom) q
  | .inr σ => geometricPullback B s m p j (relativePowerPermute B m σ) q

/-- An expression in the PEL and permutation operators, evaluated on
geometric cohomology after the factorwise degree-one selector. -/
def projectedPELAction (d q : ℕ) (e : FreeAlgebra Λ (GeometricOperator D m)) :
    Module.End Λ (cohomologyAction B s m p j q).V :=
  FreeAlgebra.lift Λ (generator B s m p j ι q) e * degreeOneSelector B s m p j d q

end Langlands.Cohomology.AbelianPower
