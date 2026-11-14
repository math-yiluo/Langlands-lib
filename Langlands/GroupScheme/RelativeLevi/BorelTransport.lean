import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.GenericFiberGeometry

/-! # Transport of relative Borel subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section IteratedPullback

variable {S U : Scheme.{u}} {k : Type u} [Field k]
  {B G : GroupScheme S} (p : U ⟶ S) (q : Spec (CommRingCat.of k) ⟶ U)
  (i : B ⟶ G)

/-- The canonical comparison identifies geometric Borels on iterated pullbacks. -/
theorem isGeometricBorelSubgroup_baseChange_comp
    (h : IsGeometricBorelSubgroup ((GroupScheme.baseChange (q ≫ p)).map i)) :
    IsGeometricBorelSubgroup
      ((GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map i)) := by
  let eB := Descent.pullbackComparison p q (q ≫ p) rfl B
  let eG := Descent.pullbackComparison p q (q ≫ p) rfl G
  have ht := (h.iso_comp eB).comp_iso eG.symm
  change IsGeometricBorelSubgroup
    ((eB.hom ≫ (GroupScheme.baseChange (q ≫ p)).map i) ≫ eG.inv) at ht
  rw [← Descent.pullbackComparison_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at ht
  exact ht

/-- Geometric Borelness on an iterated pullback gives it on the composite pullback. -/
theorem isGeometricBorelSubgroup_of_baseChange_comp
    (h : IsGeometricBorelSubgroup
      ((GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map i))) :
    IsGeometricBorelSubgroup ((GroupScheme.baseChange (q ≫ p)).map i) := by
  let eB := Descent.pullbackComparison p q (q ≫ p) rfl B
  let eG := Descent.pullbackComparison p q (q ≫ p) rfl G
  have ht := (h.iso_comp eB.symm).comp_iso eG
  change IsGeometricBorelSubgroup
    ((eB.inv ≫
      (GroupScheme.baseChange q).map ((GroupScheme.baseChange p).map i)) ≫ eG.hom) at ht
  rw [Category.assoc, Descent.pullbackComparison_naturality,
    Iso.inv_hom_id_assoc] at ht
  exact ht

end IteratedPullback

section Isomorphisms

variable {S : Scheme.{u}} {B B' G H : GroupScheme S} {i : B ⟶ G}

/-- An isomorphism of ambient groups preserves the relative Borel property. -/
theorem IsRelativeBorelSubgroup.comp_iso (hi : IsRelativeBorelSubgroup i) (e : G ≅ H) :
    IsRelativeBorelSubgroup (i ≫ e.hom) := by
  have hgeo : ∀ s : S, IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom (i ≫ e.hom) s) := by
    intro s
    change IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (i ≫ e.hom))
    rw [Functor.map_comp]
    exact (hi.residueFiber s).comp_iso
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e)
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  refine ⟨⟨hi.isRelativeParabolicSubgroup.smooth,
    hi.isRelativeParabolicSubgroup.isAffineHom, ?_,
    fun s => (hgeo s).isParabolicSubgroup⟩, hgeo⟩
  change Mono (i.hom.hom ≫ e.hom.hom.hom)
  infer_instance

/-- A source isomorphism preserves the relative Borel property. -/
theorem IsRelativeBorelSubgroup.iso_comp (hi : IsRelativeBorelSubgroup i) (e : B' ≅ B) :
    IsRelativeBorelSubgroup (e.hom ≫ i) := by
  have hgeo : ∀ s : S, IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom (e.hom ≫ i) s) := by
    intro s
    change IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (e.hom ≫ i))
    rw [Functor.map_comp]
    exact (hi.residueFiber s).iso_comp
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e)
  let : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  let : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  refine ⟨⟨?_, ?_, ?_, fun s => (hgeo s).isParabolicSubgroup⟩, hgeo⟩
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · change Mono (e.hom.hom.hom ≫ i.hom.hom)
    infer_instance

end Isomorphisms

section FieldPoint

variable {S : Scheme.{u}} {B G : GroupScheme S} {i : B ⟶ G}

/-- Relative Borels in reductive groups are geometric Borel on every
specified field-valued fibre. -/
theorem IsRelativeBorelSubgroup.fieldPoint (hi : IsRelativeBorelSubgroup i)
    (hG : IsReductive G) {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    IsGeometricBorelSubgroup ((GroupScheme.baseChange b).map i) := by
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  let c := Spec.map (fieldPointResidueMap b)
  let : Algebra (S.residueField s : Type u) k := (fieldPointResidueMap b).hom.toAlgebra
  have hred := hG.isConnectedReductive_residueFiber s
  let : Smooth ((GroupScheme.baseChange a).obj G).X.hom := hred.smooth
  let : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := hred.isAffineHom
  let : ConnectedSpace ((GroupScheme.baseChange a).obj G).X.left := hred.connectedSpace
  have h := (hi.residueFiber s).baseChange_of_smooth_affine (k := (S.residueField s : Type u)) (K := k)
  have h' := isGeometricBorelSubgroup_of_baseChange_comp a c i h
  dsimp only [a, c] at h'
  rwa [fieldPointResidueMap_factorization] at h'

end FieldPoint

section BaseChange

variable {S U : Scheme.{u}} {B G : GroupScheme S} {i : B ⟶ G}

/-- Relative Borel subgroups of reductive groups persist under arbitrary base change. -/
theorem IsRelativeBorelSubgroup.baseChange (hi : IsRelativeBorelSubgroup i)
    (hG : IsReductive G) (p : U ⟶ S) :
    IsRelativeBorelSubgroup ((GroupScheme.baseChange p).map i) := by
  let : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  let : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  have hgeo : ∀ x : U, IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom ((GroupScheme.baseChange p).map i) x) := by
    intro x
    exact isGeometricBorelSubgroup_baseChange_comp p (U.fromSpecResidueField x) i
      (hi.fieldPoint hG (U.fromSpecResidueField x ≫ p))
  refine ⟨⟨?_, ?_, ?_, fun x => (hgeo x).isParabolicSubgroup⟩, hgeo⟩
  · change Smooth (pullback.snd B.X.hom p)
    infer_instance
  · change IsAffineHom (pullback.snd B.X.hom p)
    exact MorphismProperty.pullback_snd _ _ hi.isRelativeParabolicSubgroup.isAffineHom
  · change Mono ((Over.pullback p).map i.hom.hom)
    infer_instance

variable [IsAffineHom G.X.hom]

/-- An fpqc pullback detects the relative Borel property of a supplied closed subgroup. -/
theorem IsRelativeBorelSubgroup.of_baseChange (p : U ⟶ S)
    [Flat p] [Surjective p] [QuasiCompact p] (hi : IsClosedSubgroup i)
    (h : IsRelativeBorelSubgroup ((GroupScheme.baseChange p).map i)) :
    IsRelativeBorelSubgroup i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  have hgeo : ∀ s : S, IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s) := by
    intro s
    obtain ⟨x, rfl⟩ := p.surjective s
    let a := S.fromSpecResidueField (p x)
    let c := Spec.map (p.residueFieldMap x)
    let : Algebra (S.residueField (p x) : Type u) (U.residueField x : Type u) :=
      (p.residueFieldMap x).hom.toAlgebra
    let : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := by
      change IsAffineHom (pullback.snd G.X.hom a)
      infer_instance
    apply IsGeometricBorelSubgroup.of_baseChange
      (k := (S.residueField (p x) : Type u)) (K := (U.residueField x : Type u))
      (hclosed := hi.baseChange a)
    change IsGeometricBorelSubgroup
      ((GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i))
    apply isGeometricBorelSubgroup_baseChange_comp a c i
    rw [show c ≫ a = U.fromSpecResidueField x ≫ p from
      p.SpecMap_residueFieldMap_fromSpecResidueField x]
    exact isGeometricBorelSubgroup_of_baseChange_comp p (U.fromSpecResidueField x) i
      (h.residueFiber x)
  exact ⟨⟨smooth_of_baseChange p B h.isRelativeParabolicSubgroup.smooth,
    hi.isAffineHom, Over.mono_of_mono_left _,
    fun s => (hgeo s).isParabolicSubgroup⟩, hgeo⟩

end BaseChange

/-- An actual relative Borel subgroup with its specified presentation. -/
structure RelativeBorelData {S : Scheme.{u}} (G : GroupScheme S) where
  obj : GroupScheme S
  inclusion : obj ⟶ G
  isBorel : IsRelativeBorelSubgroup inclusion

/-- Pull back an actual relative Borel subgroup in a reductive group. -/
def RelativeBorelData.baseChange {S U : Scheme.{u}} {G : GroupScheme S}
    (d : RelativeBorelData G) (hG : IsReductive G) (p : U ⟶ S) :
    RelativeBorelData ((GroupScheme.baseChange p).obj G) where
  obj := (GroupScheme.baseChange p).obj d.obj
  inclusion := (GroupScheme.baseChange p).map d.inclusion
  isBorel := d.isBorel.baseChange hG p


section BundledPullback

variable {S S' : Scheme.{u}} {B G : GroupScheme S} {i : B ⟶ G}

/-- Pullback of an actual relative Borel subgroup, retaining its source,
inclusion and relative Borel property. -/
def relativeBorelBaseChange (G : GroupScheme S) (hG : IsReductive G) (b : S' ⟶ S) :
    (Σ B : GroupScheme S, {i : B ⟶ G // IsRelativeBorelSubgroup i}) →
      Σ B' : GroupScheme S',
        {j : B' ⟶ (GroupScheme.baseChange b).obj G // IsRelativeBorelSubgroup j} :=
  fun ⟨B, i, hi⟩ =>
    ⟨(GroupScheme.baseChange b).obj B, (GroupScheme.baseChange b).map i,
      hi.baseChange hG b⟩

end BundledPullback

end Langlands.GroupScheme
