import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Pullbacks and changes of presentation of relative Borel subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.GroupScheme.RelativeLevi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

section Isomorphisms

variable {S : Scheme.{u}} {B B' G G' : GroupScheme S} {i : B ⟶ G}

/-- An ambient isomorphism preserves a relative Borel inclusion. -/
theorem IsRelativeBorelSubgroup.comp_iso
    (hi : IsRelativeBorelSubgroup i) (e : G ≅ G') :
    IsRelativeBorelSubgroup (i ≫ e.hom) := by
  refine ⟨hi.isRelativeParabolicSubgroup.comp_iso e, fun s => ?_⟩
  change IsGeometricBorelSubgroup
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (i ≫ e.hom))
  rw [Functor.map_comp]
  exact (hi.residueFiber s).comp_iso
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e)

/-- A source isomorphism preserves a relative Borel inclusion. -/
theorem IsRelativeBorelSubgroup.iso_comp
    (hi : IsRelativeBorelSubgroup i) (e : B' ≅ B) :
    IsRelativeBorelSubgroup (e.hom ≫ i) := by
  refine ⟨hi.isRelativeParabolicSubgroup.iso_comp e, fun s => ?_⟩
  change IsGeometricBorelSubgroup
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (e.hom ≫ i))
  rw [Functor.map_comp]
  exact (hi.residueFiber s).iso_comp
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e)

end Isomorphisms

section FieldPoints

variable {S : Scheme.{u}} {B G : GroupScheme S} {i : B ⟶ G}

/-- Geometric Borel properties on residue fibres hold on every specified
field-valued fibre of a reductive ambient group. -/
theorem IsRelativeBorelSubgroup.fieldPoint
    (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsGeometricBorelSubgroup ((GroupScheme.baseChange b).map i) := by
  let a := S.fromSpecResidueField (b (IsLocalRing.closedPoint k))
  let c := Spec.map (fieldPointResidueMap b)
  have h := (hi.residueFiber (b (IsLocalRing.closedPoint k))).baseChange
    (hG.isConnectedReductive_residueFiber _) c
  have ht := (h.iso_comp (baseChangeCompIso a c B)).comp_iso
    (baseChangeCompIso a c G).symm
  change IsGeometricBorelSubgroup
    (((baseChangeCompIso a c B).hom ≫
      (GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i)) ≫
        (baseChangeCompIso a c G).inv) at ht
  rw [← baseChangeCompIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at ht
  dsimp only [a, c] at ht
  rwa [fieldPointResidueMap_factorization] at ht

end FieldPoints

section Pullback

variable {S S' : Scheme.{u}} {B G : GroupScheme S} {i : B ⟶ G}

/-- Arbitrary scheme base change preserves a relative Borel inclusion in a
reductive group. -/
theorem IsRelativeBorelSubgroup.baseChange
    (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G) (b : S' ⟶ S) :
    IsRelativeBorelSubgroup ((GroupScheme.baseChange b).map i) := by
  let : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  let : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  have hf : ∀ s : S', IsGeometricBorelSubgroup
      (residueFiberHom ((GroupScheme.baseChange b).map i) s) := by
    intro s
    let c := S'.fromSpecResidueField s
    have h := hi.fieldPoint hG (c ≫ b)
    have ht := (h.iso_comp (baseChangeCompIso b c B).symm).comp_iso
      (baseChangeCompIso b c G)
    change IsGeometricBorelSubgroup
      (((baseChangeCompIso b c B).inv ≫
        (GroupScheme.baseChange (c ≫ b)).map i) ≫
          (baseChangeCompIso b c G).hom) at ht
    rw [Category.assoc, baseChangeCompIso_hom_naturality,
      Iso.inv_hom_id_assoc] at ht
    exact ht
  refine ⟨⟨?_, ?_, ?_, fun s => (hf s).isParabolicSubgroup⟩, hf⟩
  · change Smooth (pullback.snd B.X.hom b)
    infer_instance
  · change IsAffineHom (pullback.snd B.X.hom b)
    exact MorphismProperty.pullback_snd _ _ hi.isRelativeParabolicSubgroup.isAffineHom
  · change Mono ((Over.pullback b).map i.hom.hom)
    infer_instance

/-- Pullback of an actual relative Borel subgroup, retaining its source,
inclusion and relative Borel property. -/
def relativeBorelBaseChange (G : GroupScheme S) (hG : IsReductive G) (b : S' ⟶ S) :
    (Σ B : GroupScheme S, {i : B ⟶ G // IsRelativeBorelSubgroup i}) →
      Σ B' : GroupScheme S',
        {j : B' ⟶ (GroupScheme.baseChange b).obj G // IsRelativeBorelSubgroup j} :=
  fun ⟨B, i, hi⟩ =>
    ⟨(GroupScheme.baseChange b).obj B, (GroupScheme.baseChange b).map i,
      hi.baseChange hG b⟩

end Pullback

end Langlands.GroupScheme
