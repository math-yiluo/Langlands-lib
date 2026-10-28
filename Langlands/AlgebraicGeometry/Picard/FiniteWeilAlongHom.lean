import Langlands.AlgebraicGeometry.Picard.FiniteWeilPairing
import Langlands.AlgebraicGeometry.Picard.RelativePolarization
import Langlands.AbelianScheme.Tate.FiniteMonodromy

/-! # Finite Weil pairing along an actual dual-valued homomorphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "value" => finiteWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "pairing" => finiteWeilPairing preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

/-- The actual restriction of a dual-valued abelian-scheme homomorphism to torsion. -/
def finiteWeilAlongHomTorsionMap (lam : A ⟶ DA) (n : ℕ) :
    (primal n).X ⟶ (torsion (DA).toGrp (n : ℤ)).X :=
  Langlands.GroupScheme.Tate.kernelLevelMap (groupHom (A := A) (B := DA) lam) n

local notation "torsionMap" => finiteWeilAlongHomTorsionMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA


/-- Evaluate the intrinsic Weil pairing after the actual torsion map of `lam`. -/
def finiteWeilAlongHomValue (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y : T ⟶ (primal n).X) : T ⟶ (mu S n).X :=
  value n x (y ≫ torsionMap lam n)

omit [QuasiSeparatedSpace S] in
/-- The second argument is the actual torsion restriction of `lam`, as seen in the dual. -/
lemma finiteWeilAlongHom_torsion_inclusion (lam : A ⟶ DA) (n : ℕ) :
    torsionMap lam n ≫
        (torsionι (DA).toGrp (n : ℤ)).hom.hom =
      (kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom ≫
        (groupHom (A := A) (B := DA) lam).hom.hom :=
  Langlands.GroupScheme.Tate.kernelLevelMap_ι (groupHom (A := A) (B := DA) lam) n

/-- This is an actual morphism over the base from `A[n] × A[n]` to `mu_n`. -/
def finiteWeilAlongHomPairing (lam : A ⟶ DA) (n : ℕ) :
    (primal n).X ⨯ (primal n).X ⟶ (mu S n).X :=
  prod.map (𝟙 _) (torsionMap lam n) ≫ pairing n

/-- On every test scheme the value is exactly `e_n(x, lam(y))`. -/
@[simp]
lemma finiteWeilAlongHomPairing_points (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (x y : T ⟶ (primal n).X) :
    prod.lift x y ≫ finiteWeilAlongHomPairing preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA lam n =
      finiteWeilAlongHomValue preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA lam n x y := by
  unfold finiteWeilAlongHomPairing finiteWeilAlongHomValue
  rw [← Category.assoc, prod.lift_map, Category.comp_id]
  exact finiteWeilPairing_points preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n x (y ≫ torsionMap lam n)

/-- Restriction of both points restricts the same root-valued evaluation. -/
lemma finiteWeilAlongHomValue_restrict (lam : A ⟶ DA) (n : ℕ) {T U : Over S} (b : U ⟶ T)
    (x y : T ⟶ (primal n).X) :
    finiteWeilAlongHomValue preservation composition unitCoherence associativity comparison
        symmetry stability hA geometryA MA evaluationA lam n (b ≫ x) (b ≫ y) =
      b ≫ finiteWeilAlongHomValue preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA lam n x y := by
  simpa only [finiteWeilAlongHomValue, Category.assoc] using
    finiteWeilValue_restrict preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n b x (y ≫ torsionMap lam n)

/-- Pullback in the second variable retains the primal-variable homomorphism law. -/
def finiteWeilAlongHomValueHom (lam : A ⟶ DA) (n : ℕ) {T : Over S}
    (y : T ⟶ (primal n).X) :
    (T ⟶ (primal n).X) →* (T ⟶ (mu S n).X) :=
  finiteWeilValueHom preservation composition unitCoherence associativity comparison
    symmetry stability hA MA evaluationA n (y ≫ torsionMap lam n)

/-- The test-scheme formula uniquely specifies this actual scheme morphism. -/
lemma finiteWeilAlongHomPairing_unique (lam : A ⟶ DA) (n : ℕ)
    (q : (primal n).X ⨯ (primal n).X ⟶ (mu S n).X)
    (hq : ∀ (T : Over S) (x y : T ⟶ (primal n).X),
      prod.lift x y ≫ q =
        finiteWeilAlongHomValue preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA lam n x y) :
    q = finiteWeilAlongHomPairing preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA lam n := by
  have h := hq _ prod.fst prod.snd
  rw [prod.lift_fst_snd, Category.id_comp] at h
  simpa only [prod.lift_fst_snd, Category.id_comp] using h.trans
    (finiteWeilAlongHomPairing_points preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA lam n prod.fst prod.snd).symm

end Langlands.AbelianScheme
