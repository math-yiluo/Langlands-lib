import Langlands.AlgebraicGeometry.Picard.FiniteWeilBilinearity
import Langlands.AlgebraicGeometry.Picard.KernelCartierDuality
import Langlands.AlgebraicGeometry.Picard.RelativeDualKernelCharacterBijectiveStatement
import Langlands.AbelianScheme.InvertibleMultiplication

/-! # Cartier perfectness of the actual relative finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (duality : RelativeDualKernelCharacterBijectiveStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "dualTorsion" n:arg => torsion (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)
local notation "ki" n:arg =>
  relativeDualMultiplicationKernelIso preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA (n : ℤ)
local notation "chi" => dualTorsionCharacter preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "value" => finiteWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "pairing" => finiteWeilPairing preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

include duality in
/-- The actual finite Weil character is bijective on every test scheme at an invertible order. -/
lemma dualTorsionCharacter_bijective (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S) :
    Function.Bijective (fun y : T ⟶ (dualTorsion n).X => chi n y) := by
  have hbij := duality preservation composition unitCoherence associativity comparison symmetry
    stability S A A hA hA MA evaluationA MA evaluationA (multiplication A (n : ℤ))
    (multiplication_isIsogeny_of_isUnit A n hn) T
  constructor
  · intro y z h
    have hyz := hbij.injective h
    have hc := congrArg (fun t => t ≫ (ki n).hom.hom.hom) hyz
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id] using hc
  · intro χ
    obtain ⟨z, hz⟩ := hbij.surjective χ
    refine ⟨z ≫ (ki n).hom.hom.hom, ?_⟩
    change chi n (z ≫ (ki n).hom.hom.hom) = χ
    unfold dualTorsionCharacter
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
    exact hz

/-- The intrinsic finite Weil character as an additive equivalence on actual test-scheme points. -/
def finiteWeilCartierEquiv (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S) :
    Additive (T ⟶ (dualTorsion n).X) ≃+
      (Cartier.characters (primal n)).obj (op T) :=
  AddEquiv.ofBijective
    (dualTorsionCharacterAddHom preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA n T)
    (dualTorsionCharacter_bijective preservation composition unitCoherence associativity comparison
      symmetry stability duality hA MA evaluationA n hn T)

@[simp] lemma finiteWeilCartierEquiv_apply (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (y : Additive (T ⟶ (dualTorsion n).X)) :
    finiteWeilCartierEquiv preservation composition unitCoherence associativity comparison
      symmetry stability duality hA MA evaluationA n hn T y = chi n y.toMul := rfl

/-- The actual dual torsion represents the Cartier dual of actual primal torsion. -/
def finiteWeilCartierIso (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    additivePoints (dualTorsion n) ≅ Cartier.characters (primal n) :=
  NatIso.ofComponents
    (fun T => (finiteWeilCartierEquiv preservation composition unitCoherence associativity comparison
      symmetry stability duality hA MA evaluationA n hn T.unop).toAddCommGrpIso)
    (by
      intro T U b
      ext y
      exact dualTorsionCharacter_restrict preservation composition unitCoherence associativity
        comparison symmetry stability hA MA evaluationA n b.unop y.toMul)

/-- The forward map is precisely the character used by the published finite Weil pairing. -/
@[simp] lemma finiteWeilCartierIso_hom_app (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (y : Additive (T ⟶ (dualTorsion n).X)) :
    (finiteWeilCartierIso preservation composition unitCoherence associativity comparison
      symmetry stability duality hA MA evaluationA n hn).hom.app (op T) y = chi n y.toMul := rfl

/-- Evaluation of the perfect character is the original root-valued finite Weil pairing. -/
lemma finiteWeilCartierIso_muEvaluation (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (x : T ⟶ (primal n).X) (y : T ⟶ (dualTorsion n).X) :
    Cartier.muEvaluation n (torsion_multiplication_eq_one A.toGrp (n : ℤ))
      ((finiteWeilCartierIso preservation composition unitCoherence associativity comparison
        symmetry stability duality hA MA evaluationA n hn).hom.app (op T) (Additive.ofMul y)) x =
      value n x y := rfl

/-- The same Cartier perfectness with actual homomorphisms to the multiplicative group over tests. -/
def finiteWeilCharacterHomIso (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    additivePoints (dualTorsion n) ≅ Cartier.characterHomFunctor (primal n) :=
  finiteWeilCartierIso preservation composition unitCoherence associativity comparison
    symmetry stability duality hA MA evaluationA n hn ≪≫ Cartier.characterHomNatIso (primal n)

end Langlands.AbelianScheme
