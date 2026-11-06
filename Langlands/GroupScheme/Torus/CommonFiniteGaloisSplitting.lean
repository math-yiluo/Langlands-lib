import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Mathlib.FieldTheory.SeparableDegree

/-! # A common finite Galois splitting field for two actual tori -/

noncomputable section

open AlgebraicGeometry

universe u

namespace Langlands.GroupScheme

/-- A single finite Galois extension splitting two given group schemes. -/
structure TorusCommonFiniteGaloisSplittingData
    (k : Type u) [Field k]
    (T Q : GroupScheme (Spec (CommRingCat.of k))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [finiteDimensional : FiniteDimensional k carrier]
  [isGalois : IsGalois k carrier]
  split_left : IsSplitTorus ((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k carrier)))).obj T)
  split_right : IsSplitTorus ((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k carrier)))).obj Q)

attribute [instance] TorusCommonFiniteGaloisSplittingData.field
  TorusCommonFiniteGaloisSplittingData.algebra
  TorusCommonFiniteGaloisSplittingData.finiteDimensional
  TorusCommonFiniteGaloisSplittingData.isGalois

/-- Choose one finite Galois splitting field for two actual field tori. -/
def IsTorus.commonFiniteGaloisSplitting
    {k : Type u} [Field k]
    {T Q : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) (hQ : IsTorus Q) :
    TorusCommonFiniteGaloisSplittingData k T Q := by
  classical
  apply Classical.choice
  obtain ⟨K, hK, hAK, hfinK, hgalK, hTK⟩ := torusFiniteGaloisSplitting k T hT
  have hQK := IsTorus.baseChange_of_isAlgebraic k K Q hQ
  obtain ⟨L, hL, hAL, hfinL, hgalL, hQL⟩ :=
    torusFiniteGaloisSplitting K _ hQK
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional k L := FiniteDimensional.trans k K L
  let : Algebra.IsSeparable k L := Algebra.IsSeparable.trans k K L
  have hTL := hTK.baseChange_fieldTower k K L T
  have hQL' := (IsSplitTorus.baseChange_fieldTower_iff k K L Q).2 hQL
  let f : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let E := IntermediateField.normalClosure k L (SeparableClosure k)
  exact ⟨{
    carrier := E
    field := inferInstance
    algebra := inferInstance
    finiteDimensional := inferInstance
    isGalois := inferInstance
    split_left := hTL.baseChange_fieldTower k L E T
    split_right := hQL'.baseChange_fieldTower k L E Q }⟩

end Langlands.GroupScheme
