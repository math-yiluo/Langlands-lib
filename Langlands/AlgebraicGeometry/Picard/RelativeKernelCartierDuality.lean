import Langlands.AlgebraicGeometry.Picard.KernelCartierDuality
import Langlands.AlgebraicGeometry.Picard.RelativeDualKernelCharacterBijectiveStatement

/-! # Relative Cartier duality as a group-valued natural isomorphism -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

section Relative

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (duality : RelativeDualKernelCharacterBijectiveStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (f : A ⟶ B)

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)
local notation "beta" => dualKernelPointCharacter hA stability f hB preservation composition
  unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB
local notation "betaAdd" => dualKernelPointCharacterAddHom hA stability f hB preservation
  composition unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB

variable (hf : IsIsogeny f)

/-- Actual relative Cartier duality as an additive equivalence on every test scheme. -/
def relativeDualKernelCharacterEquiv (T : Over S) :
    Additive (T ⟶ (GroupScheme.kernel df).X) ≃+
      (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  AddEquiv.ofBijective (betaAdd T)
    (duality preservation composition unitCoherence associativity
      comparison symmetry stability S A B hA hB MA evaluationA MB evaluationB f hf T)

@[simp] theorem relativeDualKernelCharacterEquiv_apply (T : Over S)
    (x : Additive (T ⟶ (GroupScheme.kernel df).X)) :
    relativeDualKernelCharacterEquiv preservation composition unitCoherence associativity
      comparison symmetry stability duality hA hB MA evaluationA MB evaluationB f hf T x =
      beta T x.toMul := rfl

/-- The actual dual kernel represents the relative Cartier-character functor as groups. -/
def relativeDualKernelCartierIso :
    additivePoints (GroupScheme.kernel df) ≅ Cartier.characters (kernelCommGroupScheme f) :=
  NatIso.ofComponents
    (fun T => (relativeDualKernelCharacterEquiv preservation composition unitCoherence
      associativity comparison symmetry stability duality hA hB MA evaluationA MB evaluationB f hf
      T.unop).toAddCommGrpIso)
    (by
      intro T U b
      ext x
      exact dualKernelPointCharacter_restrict hA stability f hB b.unop preservation composition
        unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB x.toMul)

/-- The forward map of the isomorphism is exactly the normalized Poincare character. -/
@[simp] theorem relativeDualKernelCartierIso_hom :
    (relativeDualKernelCartierIso preservation composition unitCoherence associativity comparison
      symmetry stability duality hA hB MA evaluationA MB evaluationB f hf).hom =
      dualKernelCharacterAddNatTrans preservation composition unitCoherence associativity
        comparison symmetry stability hA hB MA evaluationA MB evaluationB f := by
  ext T x
  rfl

/-- The same Cartier duality with actual homomorphisms over each test scheme as target. -/
def relativeDualKernelCharacterHomIso :
    additivePoints (GroupScheme.kernel df) ≅
      Cartier.characterHomFunctor (kernelCommGroupScheme f) :=
  relativeDualKernelCartierIso preservation composition unitCoherence associativity comparison
    symmetry stability duality hA hB MA evaluationA MB evaluationB f hf ≪≫
      Cartier.characterHomNatIso (kernelCommGroupScheme f)

include hf duality in
/-- Every character, including on nonreduced tests, comes from a unique actual dual-kernel point. -/
theorem relativeDualKernelCharacter_existsUnique (T : Over S)
    (chi : (Cartier.characters (kernelCommGroupScheme f)).obj (op T)) :
    ∃! x : T ⟶ (GroupScheme.kernel df).X, beta T x = chi := by
  obtain ⟨x, hx⟩ := (relativeDualKernelCharacterEquiv preservation composition unitCoherence
    associativity comparison symmetry stability duality hA hB MA evaluationA MB evaluationB f hf
    T).surjective chi
  refine ⟨x.toMul, hx, ?_⟩
  intro y hy
  exact (duality preservation composition unitCoherence associativity
    comparison symmetry stability S A B hA hB MA evaluationA MB evaluationB f hf T).injective
      (hy.trans hx.symm)

end Relative
end Langlands.AbelianScheme
