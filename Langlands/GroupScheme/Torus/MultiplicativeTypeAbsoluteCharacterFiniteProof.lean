import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteCharacterStatement
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite generation of actual absolute-Galois characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

theorem multiplicativeTypeAbsoluteCharacterFinite :
    MultiplicativeTypeAbsoluteCharacterFiniteStatement.{u} := by
  intro k _ T hT
  obtain ⟨K, hK, hA, M, hM, hfg, ⟨d⟩⟩ := hT
  let Ω := SeparableClosure k
  let E := AlgebraicClosure K
  let f : Ω →ₐ[k] E := IsAlgClosed.lift
  let : Algebra Ω E := f.toRingHom.toAlgebra
  let : IsScalarTower k Ω E :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let TΩ := (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T
  let TΩE := (CommGroupScheme.baseChange (algebraBaseMap Ω E)).obj TΩ
  let e : TΩE.toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of E) M).toGrp :=
    (baseChangeFieldTowerIso k Ω E T.toGrp).symm ≪≫
      baseChangeFieldTowerIso k K E T.toGrp ≪≫
      (GroupScheme.baseChange (algebraBaseMap K E)).mapIso d ≪≫
      Diagonalizable.baseChangeIso (algebraBaseMap K E) M
  let c : M ≃+ characterLattice TΩE :=
    (DiagonalizableCharacter.evalCharacterEquiv E M).trans
      (characterLattice.comapIso e)
  let : AddGroup.FG (characterLattice TΩE) :=
    AddGroup.fg_of_surjective (f := c.toAddMonoidHom) c.surjective
  let : Module.Finite ℤ (characterLattice TΩE) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact Module.Finite.of_injective
    (characterLattice.baseChange (algebraBaseMap Ω E) TΩ).toIntLinearMap
    (characterLattice.algebraBaseChange_injective Ω E TΩ)

end Langlands.GroupScheme
