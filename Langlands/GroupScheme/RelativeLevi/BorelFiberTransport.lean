import Langlands.GroupScheme.RelativeLevi.BorelFieldTransport
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange

/-! # Field fibres and base change of the Borel locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {G P : GroupScheme S} {i : P ⟶ G}

/-- The geometric Borel condition respects the actual comparison between
successive pullbacks and an equal composite pullback. -/
theorem isGeometricBorelSubgroup_pullbackComparison_iff
    {k : Type u} [Field k] (f : S' ⟶ S)
    (q : Spec (CommRingCat.of k) ⟶ S') (r : Spec (CommRingCat.of k) ⟶ S)
    (h : q ≫ f = r) :
    IsGeometricBorelSubgroup ((baseChange q).map ((baseChange f).map i)) ↔
      IsGeometricBorelSubgroup ((baseChange r).map i) := by
  let eP := Descent.pullbackComparison f q r h P
  let eG := Descent.pullbackComparison f q r h G
  constructor
  · intro hi
    have hb := (hi.iso_comp eP.symm).comp_iso eG
    change IsGeometricBorelSubgroup
      ((eP.inv ≫ (baseChange q).map ((baseChange f).map i)) ≫ eG.hom) at hb
    rw [Category.assoc, Descent.pullbackComparison_naturality,
      Iso.inv_hom_id_assoc] at hb
    exact hb
  · intro hi
    have hb := (hi.iso_comp eP).comp_iso eG.symm
    change IsGeometricBorelSubgroup
      ((eP.hom ≫ (baseChange r).map i) ≫ eG.inv) at hb
    rw [← Descent.pullbackComparison_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at hb
    exact hb

/-- A field-valued fibre is geometric Borel exactly when its residue-field
fibre is geometric Borel. -/
theorem isGeometricBorelSubgroup_fieldPoint_iff
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    IsGeometricBorelSubgroup ((baseChange f).map i) ↔
      IsGeometricBorelSubgroup
        (RelativeLevi.residueFiberHom i (f (IsLocalRing.closedPoint k))) := by
  let s := f (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo f)
  let : Algebra (S.residueField s) k := φ.hom.toAlgebra
  have hf : Spec.map φ ≫ S.fromSpecResidueField s = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S f
  rw [← isGeometricBorelSubgroup_pullbackComparison_iff
    (i := i) (S.fromSpecResidueField s) (Spec.map φ) f hf]
  exact isGeometricBorelSubgroup_baseChange_field_iff
    (k := S.residueField s) (K := k) (i := RelativeLevi.residueFiberHom i s)
    (hG.isConnectedReductive_residueFiber s) (hi.residueFiber s).isClosedSubgroup

/-- The residue-field Borel locus pulls back along every scheme morphism. -/
theorem isGeometricBorelSubgroup_residueFiber_baseChange_iff
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (b : S' ⟶ S) (s' : S') :
    IsGeometricBorelSubgroup
        (RelativeLevi.residueFiberHom ((baseChange b).map i) s') ↔
      IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i (b s')) := by
  let a := S'.fromSpecResidueField s'
  have h := (isGeometricBorelSubgroup_pullbackComparison_iff
    (i := i) b a (a ≫ b) rfl).trans
      (isGeometricBorelSubgroup_fieldPoint_iff hG hi (a ≫ b))
  have he : (a ≫ b) (IsLocalRing.closedPoint (S'.residueField s')) = b s' := by
    change b (S'.fromSpecResidueField s' _) = b s'
    rw [Scheme.fromSpecResidueField_apply]
  change IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom
      ((baseChange b).map i) s') ↔
    IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom i
        ((a ≫ b) (IsLocalRing.closedPoint (S'.residueField s')))) at h
  exact h.trans (Iff.of_eq (congrArg (fun s : S =>
    IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s)) he))

end Langlands.GroupScheme
