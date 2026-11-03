import Langlands.Global.AdelicPositiveDecompositionStatement
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndexProof

/-! # Construct positive decomposition from central character detection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (hS : CentralSplitTorusCharacterStatement.{u})
variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable [IsAffineHom G.X.hom]
variable (hG : IsConnectedReductive G)
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G) (hi : IsSplitComponent i)

/-- Construct the actual multiplication equivalence for any split component,
using central split-torus detection only for restriction injectivity. -/
def splitComponentNormOneDecomposition :
    intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ* AdelicGroupPoints F G := by
  classical
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hinj : Function.Injective (characterRestrict i) :=
    characterRestrict_injective_of_centralSplitTorusCharacter hS hG hi
  letI : (characterRestrict i).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG T i hi
  let I : Type u := hi.1.1.1.choose
  letI : Finite I := hi.1.1.1.choose_spec.choose
  letI : Fintype I := Fintype.ofFinite I
  let e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I :=
    hi.1.1.1.choose_spec.choose_spec.some
  exact normOneDecompositionMulEquiv F G T i hinj I e hi.1.2

@[simp] theorem splitComponentNormOneDecomposition_apply
    (p : intrinsicSubgroup F T × normOneSubgroup F G) :
    splitComponentNormOneDecomposition hS F G hG T i hi p =
      positivePointMap F G T i p.1 * p.2 := rfl

include hS hG hi in
/-- The constructed equivalence has the required multiplication formula. -/
theorem hasPositiveNormOneDecomposition_of_centralSplitTorusCharacter :
    HasPositiveNormOneDecomposition F G T i :=
  ⟨splitComponentNormOneDecomposition hS F G hG T i hi,
    splitComponentNormOneDecomposition_apply hS F G hG T i hi⟩

include hS in
/-- The sole open input of this reduction is the named algebraic detection
target; split-component existence and finite index are imported proofs. -/
theorem adelicPositiveDecomposition_of_centralSplitTorusCharacter :
    AdelicPositiveDecompositionStatement.{u} := by
  intro F _ _ G _ _ hG
  obtain ⟨T, i, hi⟩ := (splitComponentStatement F G hG).1
  exact ⟨T, i, hi,
    hasPositiveNormOneDecomposition_of_centralSplitTorusCharacter hS F G hG T i hi⟩

end Langlands.Global.PositiveRealTorus
