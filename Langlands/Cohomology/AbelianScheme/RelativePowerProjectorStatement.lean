import Langlands.AbelianScheme.RelativePower
import Langlands.Cohomology.AbelianScheme.RelativeAdicMultiplicationStatement
import Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology
import Langlands.Geometry.EtaleDerivedGlobalPullback
import Langlands.Shimura.PEL.CohomologicalProjectorPolynomial
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Topology.KrullDimension

/-!
# The degree-one selector on an abelian power

Harris–Taylor III.2, p. 98, uses the actual factorwise multiplication-by-two
pullbacks to compare a single projected Leray row with projected total
cohomology. This statement uses the selector before the algebraic coefficient
idempotent and the Tate twist.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry EtaleDerivedSections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe wS wX wR

namespace Langlands.Cohomology.AbelianRelativeEtale

open Langlands.AbelianScheme Langlands.Shimura.PEL.CohomologicalProjector

variable (p : ℕ) [Fact p.Prime]

local notation "Zp" => ℤ_[p]
local notation "Qp" => ℚ_[p]

private abbrev rationalization := ModuleCat.extendScalars (algebraMap Zp Qp)

private abbrev constantCoefficients (X : Scheme.{0}) : ℕᵒᵖ ⥤ ModuleSheaf X Zp :=
  EtaleAdicSystem.ellPowerConstantSystem X p (ModuleCat.of Zp Zp)

/-- The rationalization of the actual adic cohomology of the constant system. -/
def rationalAdicCohomology (X : Scheme.{0}) (q : ℕ) : ModuleCat Qp :=
  (rationalization p).obj
    ((EtaleAdicCohomology.adicCohomology X Zp q).obj (constantCoefficients p X))

/-- Coefficient reductions before taking constant sheaves. -/
private abbrev reductions : ℕᵒᵖ ⥤ ModuleCat Zp :=
  (Langlands.Coefficients.AdicSystem.functor (Ideal.span {(p : Zp)})).obj
    (ModuleCat.of Zp Zp)

/-- Global pullback on the rationalized cohomology of the constant system. -/
def rationalAdicCohomologyPullback {X Y : Scheme.{0}} (a : Y ⟶ X) (q : ℕ)
    [HasDerivedCategory.{wX} (ModuleSheaf X ℤ_[p])]
    [HasDerivedCategory.{wX} (ModuleSheaf Y ℤ_[p])]
    [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])] :
    rationalAdicCohomology p X q ⟶ rationalAdicCohomology p Y q :=
  let pull : constantCohomology X Zp q ⟶ constantCohomology Y Zp q :=
    Functor.whiskerLeft _ (EtaleDerivedGlobalPullback.cohomologyPullback a Zp q) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (EtaleInverseImage.inverseImageConstantIso a Zp).hom _
  (rationalization p).map (limMap (Functor.whiskerLeft (reductions p) pull))

/-- `H^i(S, R^j f_* ℚ_p)` calculated by finite coefficients followed
by the limit and rationalization. -/
def rationalAdicLerayTerm {S X : Scheme.{0}} (f : X ⟶ S) (i j : ℕ) : ModuleCat Qp :=
  (rationalization p).obj ((EtaleAdicCohomology.adicCohomology S Zp i).obj
    (relativeAdicCohomologySystem p f j))

/-- The actual action on a rationalized Leray term induced by an endomorphism over the base. -/
def rationalAdicLerayTermPullback {S X : Scheme.{0}} {f : X ⟶ S}
    (a : X ⟶ X) (h : a ≫ f = f) (i j : ℕ)
    [HasDerivedCategory.{wS} (ModuleSheaf S ℤ_[p])]
    [HasDerivedCategory.{wX} (ModuleSheaf X ℤ_[p])] :
    rationalAdicLerayTerm p f i j ⟶ rationalAdicLerayTerm p f i j :=
  (rationalization p).map ((EtaleAdicCohomology.adicCohomology S Zp i).map
    (relativeAdicCohomologyPullback.{wS, wX, wX} p a h j))

variable {S : Scheme.{0}} (A : AbelianScheme S) (m g : ℕ)

private abbrev power := relativePower A m

/-- The geometric fibres of the abelian scheme have dimension at most `g`. -/
def HasBoundedGeometricFibreDimension : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S),
    topologicalKrullDim (pullback A.X.hom s : Scheme.{0}) ≤ g

variable [HasDerivedCategory.{wS} (ModuleSheaf S ℤ_[p])]
variable [HasDerivedCategory.{wX} (ModuleSheaf (power A m).left ℤ_[p])]
variable [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])]

/-- The polynomial composed on the actual factor pullbacks on a Leray term. -/
def lerayDegreeOneSelector (i j : ℕ) :
    Module.End Qp (rationalAdicLerayTerm p (power A m).hom i j) :=
  degreeOneEndomorphism Qp (2 * g) fun x : Fin m =>
    (rationalAdicLerayTermPullback.{wS, wX} p (relativePowerDouble A m x).left
      (relativePowerDouble A m x).w i j).hom

/-- The same polynomial composed on the factor pullbacks on total cohomology. -/
def totalDegreeOneSelector (q : ℕ) :
    Module.End Qp (rationalAdicCohomology p (power A m).left q) :=
  degreeOneEndomorphism Qp (2 * g) fun x : Fin m =>
    (rationalAdicCohomologyPullback.{wX, wR} p (relativePowerDouble A m x).left q).hom

/-- The multiplication selector is idempotent and supported in a single
relative row. In total degree `i+m` its image is isomorphic to the
selected Leray term in bidegree `(i,m)`. -/
def RelativePowerDegreeOneProjectorStatement {k : Type} [Field k] [IsAlgClosed k]
    (s : S ⟶ Spec (CommRingCat.of k)) [IsProper s] : Prop :=
  IsUnit (p : Γ(S, ⊤)) → HasBoundedGeometricFibreDimension A g →
  (∀ i j : ℕ, IsIdempotentElem (lerayDegreeOneSelector.{wS, wX} p A m g i j) ∧
    (j ≠ m → lerayDegreeOneSelector.{wS, wX} p A m g i j = 0)) ∧
  (∀ q : ℕ, IsIdempotentElem (totalDegreeOneSelector.{wX, wR} p A m g q)) ∧
  ∀ i : ℕ, Nonempty ((lerayDegreeOneSelector.{wS, wX} p A m g i m).range ≃ₗ[Qp]
    (totalDegreeOneSelector.{wX, wR} p A m g (i + m)).range)

end Langlands.Cohomology.AbelianRelativeEtale
