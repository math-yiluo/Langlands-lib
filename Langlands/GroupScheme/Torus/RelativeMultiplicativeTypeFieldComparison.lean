import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Field fibres of relative groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

/-- Actual splitting data for a group over a field: an extension field,
a finitely generated abelian character group, and a diagonalization. -/
structure FieldDiagonalization {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  extensionField : Type u
  [field : Field extensionField]
  [algebra : Algebra k extensionField]
  characterGroup : Type u
  [addCommGroup : AddCommGroup characterGroup]
  [finiteGeneration : AddGroup.FG characterGroup]
  iso : ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k extensionField)))).obj G) ≅
    (Diagonalizable.groupScheme (CommRingCat.of extensionField) characterGroup).toGrp

attribute [instance] FieldDiagonalization.field FieldDiagonalization.algebra
  FieldDiagonalization.addCommGroup FieldDiagonalization.finiteGeneration

/-- An fppf splitting cover over a field supplies a splitting field, by taking
the residue field of any point above the unique point of the base. -/
theorem IsMultiplicativeType.nonempty_fieldDiagonalization
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsMultiplicativeType G) : Nonempty (FieldDiagonalization G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨a, y, _hy⟩ := 𝒰.exists_eq (IsLocalRing.closedPoint k)
  let K := (𝒰.X a).residueField y
  let r := (𝒰.X a).fromSpecResidueField y
  let b := r ≫ 𝒰.f a
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hd : IsDiagonalizable ((GroupScheme.baseChange b).obj G) :=
    IsDiagonalizable.of_iso (baseChangeCompIso (𝒰.f a) r G)
      ((h𝒰 a).baseChange r)
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hd
  refine ⟨{ extensionField := K, characterGroup := Λ, iso := ?_ }⟩
  change ((GroupScheme.baseChange (Spec.map (Spec.preimage b))).obj G) ≅
    (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp
  rw [Spec.map_preimage]
  exact e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec (CommRingCat.of K))) Λ

/-- Choose actual field splitting data from a relative multiplicative-type
splitting cover. -/
def IsMultiplicativeType.fieldDiagonalization
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsMultiplicativeType G) : FieldDiagonalization G :=
  Classical.choice hG.nonempty_fieldDiagonalization

/-- The actual field diagonalization gives the published field-level
multiplicative-type predicate. -/
theorem IsMultiplicativeType.isFieldMultiplicativeType
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsMultiplicativeType G) :
    Langlands.GroupScheme.IsMultiplicativeType G := by
  let d := hG.fieldDiagonalization
  exact ⟨d.extensionField, inferInstance, inferInstance, d.characterGroup,
    inferInstance, inferInstance, ⟨d.iso⟩⟩

/-- Every field-valued fibre of a relative group of multiplicative type has
the field-level multiplicative-type predicate. -/
theorem IsMultiplicativeType.field_baseChange
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsMultiplicativeType G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    Langlands.GroupScheme.IsMultiplicativeType ((GroupScheme.baseChange b).obj G) :=
  (hG.baseChange b).isFieldMultiplicativeType

end Langlands.GroupScheme.RelativeMultiplicativeType
