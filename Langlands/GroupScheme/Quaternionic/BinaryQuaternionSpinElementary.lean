import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinLift
import Langlands.GroupScheme.SpecialLinearBinaryAmbientGeneration

/-! # The split binary spin image in the parabolic elementary subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.BinarySpinLift

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- Every rational point of the actual SL₂ lift is elementary in the supplied spin group. -/
theorem specialLinear_range_le_elementary :
    (rationalPoints.map (specialLinear σ hdim hsym h hπ hsc)).range ≤
      parabolicElementarySubgroup S :=
  SpecialLinear.BinaryRoot.rationalPoints_range_le_parabolicElementarySubgroup
    hπ.isSimplyConnected.isSemisimple.isConnectedReductive
    (specialLinear σ hdim hsym h hπ hsc)

/-- The original SL₂ point map with its codomain restricted to the actual elementary subgroup. -/
def specialLinearToElementary :
    rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)) →*
      parabolicElementarySubgroup S :=
  (rationalPoints.map (specialLinear σ hdim hsym h hπ hsc)).codRestrict
    (parabolicElementarySubgroup S) fun x =>
      specialLinear_range_le_elementary σ hdim hsym h hπ hsc ⟨x, rfl⟩

@[simp] theorem specialLinearToElementary_coe
    (x : rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K))) :
    (specialLinearToElementary σ hdim hsym h hπ hsc x : rationalPoints S) =
      rationalPoints.map (specialLinear σ hdim hsym h hπ hsc) x := rfl

/-- Every rational point of the scalar spin cocharacter is elementary. -/
theorem scalar_range_le_elementary :
    (rationalPoints.map (scalar σ hdim hsym h hπ hsc)).range ≤
      parabolicElementarySubgroup S := by
  rintro _ ⟨x, rfl⟩
  have hx := specialLinear_range_le_elementary σ hdim hsym h hπ hsc
    ⟨rationalPoints.map (SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K)) x, rfl⟩
  simpa only [scalar, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using hx

/-- The scalar cocharacter on rational points, with codomain in the elementary subgroup. -/
def scalarToElementary :
    rationalPoints (Gm (Spec (CommRingCat.of K))).toGrp →*
      parabolicElementarySubgroup S :=
  (rationalPoints.map (scalar σ hdim hsym h hπ hsc)).codRestrict
    (parabolicElementarySubgroup S) fun x =>
      scalar_range_le_elementary σ hdim hsym h hπ hsc ⟨x, rfl⟩

@[simp] theorem scalarToElementary_coe
    (x : rationalPoints (Gm (Spec (CommRingCat.of K))).toGrp) :
    (scalarToElementary σ hdim hsym h hπ hsc x : rationalPoints S) =
      rationalPoints.map (scalar σ hdim hsym h hπ hsc) x := rfl

/-- The scalar unit homomorphism `Kˣ → S(K)⁺` from the actual rational Gm point model. -/
def scalarUnitsToElementary : Kˣ →* parabolicElementarySubgroup S :=
  (scalarToElementary σ hdim hsym h hπ hsc).comp
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm.toMonoidHom

@[simp] theorem scalarUnitsToElementary_coe (t : Kˣ) :
    (scalarUnitsToElementary σ hdim hsym h hπ hsc t : rationalPoints S) =
      rationalPoints.map (scalar σ hdim hsym h hπ hsc)
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm t) := rfl

/-- In particular, the scalar spin lift of the unit minus one is elementary. -/
theorem scalar_neg_one_mem_elementary :
    rationalPoints.map (scalar σ hdim hsym h hπ hsc)
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm (-1 : Kˣ)) ∈
      parabolicElementarySubgroup S :=
  (scalarUnitsToElementary σ hdim hsym h hπ hsc (-1)).property

end Langlands.GroupScheme.Quaternionic.BinarySpinLift
