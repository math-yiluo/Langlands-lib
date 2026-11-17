import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFieldStatement

/-! # Field-valued fibres of relative groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeMultiplicativeType

/-- An fppf diagonalizing cover over a field supplies a splitting field by
choosing a residue field of a point of the cover. -/
theorem IsMultiplicativeType.isMultiplicativeType {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsMultiplicativeType G) :
    _root_.Langlands.GroupScheme.IsMultiplicativeType G := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨a, y, _hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint k)
  let K := (𝒰.X a).residueField y
  let b := (𝒰.X a).fromSpecResidueField y ≫ 𝒰.f a
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  obtain ⟨M, hM, hfg, ⟨e⟩⟩ := h𝒰 a
  refine ⟨K, inferInstance, inferInstance, M, hM, hfg, ⟨?_⟩⟩
  change (GroupScheme.baseChange (Spec.map (Spec.preimage b))).obj G ≅ _
  rw [Spec.map_preimage]
  exact baseChangeCompIso (𝒰.f a) ((𝒰.X a).fromSpecResidueField y) G ≪≫
    (GroupScheme.baseChange ((𝒰.X a).fromSpecResidueField y)).mapIso e ≪≫
      diagonalizableBaseChangeIso ((𝒰.X a).fromSpecResidueField y) M ≪≫
        (Diagonalizable.relativeModelIso (CommRingCat.of K) M).symm

/-- A field extension and an actual finite-character diagonalization of a group
scheme over a field, retaining the witnesses of field-level multiplicative type. -/
structure FieldSplittingData {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  splittingField : Type u
  [fieldStructure : Field splittingField]
  [fieldAlgebra : Algebra k splittingField]
  characters : Type u
  [characterGroup : AddCommGroup characters]
  [finitelyGenerated : AddGroup.FG characters]
  iso : ((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k splittingField)))).obj G) ≅
      (Diagonalizable.groupScheme (CommRingCat.of splittingField) characters).toGrp

attribute [instance] FieldSplittingData.fieldStructure FieldSplittingData.fieldAlgebra
  FieldSplittingData.characterGroup FieldSplittingData.finitelyGenerated

/-- Choose an actual splitting field and diagonalization from a relative
diagonalizing cover over a field. No uniqueness or naturality is asserted. -/
def IsMultiplicativeType.fieldSplitting {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsMultiplicativeType G) :
    FieldSplittingData G :=
  Classical.choice (by
    obtain ⟨K, hK, aK, M, hM, hfg, ⟨e⟩⟩ := hG.isMultiplicativeType
    exact ⟨{
      splittingField := K
      fieldStructure := hK
      fieldAlgebra := aK
      characters := M
      characterGroup := hM
      finitelyGenerated := hfg
      iso := e }⟩)

/-- Every field-valued fibre of a relative group of multiplicative type is
of multiplicative type in the field-level sense. -/
theorem IsMultiplicativeType.fieldFiber {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsMultiplicativeType G) {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    _root_.Langlands.GroupScheme.IsMultiplicativeType ((GroupScheme.baseChange b).obj G) :=
  (hG.baseChange b).isMultiplicativeType

/-- In particular every geometric fibre retains multiplicative type. -/
theorem IsMultiplicativeType.geometricFiber {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsMultiplicativeType G) (s : S) :
    _root_.Langlands.GroupScheme.IsMultiplicativeType
      (_root_.Langlands.GroupScheme.geometricFiber G s) :=
  hG.fieldFiber (geometricPoint S s)

end Langlands.GroupScheme.RelativeMultiplicativeType

namespace Langlands.GroupScheme

/-- The comparison for all field-valued fibres. -/
theorem relativeMultiplicativeTypeField :
    RelativeMultiplicativeTypeFieldStatement.{u} :=
  fun _ _ hG _ _ b => hG.fieldFiber b

end Langlands.GroupScheme
