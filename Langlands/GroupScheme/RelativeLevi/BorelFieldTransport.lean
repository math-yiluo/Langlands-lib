import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.Descent.QuasiSplitDatum
import Langlands.GroupScheme.SolvablePoints
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof

/-! # Field transport for geometric Borel fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section ClosedFields

variable {k K : Type u} [Field k] [Field K] [IsAlgClosed k]
  [Algebra k K] {B G : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}
  [IsAffineHom G.X.hom]

/-- An extension of an algebraically closed field reflects the Borel property of
an actual closed inclusion. -/
theorem IsBorelSubgroup.of_baseChange_of_isAlgClosed
    (hi : IsBorelSubgroup
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i) : IsBorelSubgroup i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := baseChange b
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let : Epi b := Flat.epi_of_flat_of_surjective b
  let : IsClosedImmersion i.hom.hom.left := hclosed
  let : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hsol : IsSolvableGroupScheme B := by
    apply (isSolvableGroupScheme_iff_rationalPoints B).mpr
    let : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (F.obj B).X) :=
      hi.isSolvableGroupScheme.rationalPoints
    exact Group.isSolvable_of_isSolvable_injective
      (f := basePointExtension b B) (basePointExtension_injective b B)
  refine ⟨hclosed, smooth_of_baseChange b B hi.smooth,
    connectedSpace_of_baseChange b B hi.connectedSpace, hsol, ?_⟩
  intro C j f hj hsm hconn hsolC hf
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth C.X.hom := hsm
  let : ConnectedSpace C.X.left := hconn
  have : IsIso (F.map f) := hi.maximal (F.obj C) (F.map j) (F.map f)
    (hj.baseChange b) (show Smooth (pullback.snd C.X.hom b) from inferInstance)
    (C.connectedSpace_baseChange_of_smooth_affine b)
    (solvableFieldExtensionStatement k K b C hsm hsolC)
    (by rw [← F.map_comp, hf])
  exact isIso_of_baseChange b f

end ClosedFields

section Fields

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {B G : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

/-- Geometric Borel inclusions in connected reductive groups persist under
arbitrary field extensions. -/
theorem IsGeometricBorelSubgroup.baseChange_field
    (hi : IsGeometricBorelSubgroup i) (hG : IsConnectedReductive G) :
    IsGeometricBorelSubgroup
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let a := toAlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c := toAlgebraicClosure K
  let d := algebraicClosureBaseMap k K
  let e := algebraicClosureBaseChangeIso k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  let : IsAffineHom ((baseChange a).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom a))
  have hbar : IsBorelSubgroup ((baseChange d).map ((baseChange a).map i)) :=
    borelAlgClosedFieldExtensionStatement (AlgebraicClosure k) (AlgebraicClosure K)
      ((baseChange a).obj G) inferInstance
      (show Smooth (pullback.snd G.X.hom a) from inferInstance)
      hG.connectedSpace_toAlgebraicClosure _ _ hi.2
  have hgeom : IsBorelSubgroup ((baseChange c).map ((baseChange b).map i)) := by
    have h := (hbar.iso_comp (e.app B).symm).comp_iso (e.app G)
    change IsBorelSubgroup (((e.app B).inv ≫
      (baseChange d).map ((baseChange a).map i)) ≫ (e.app G).hom) at h
    rw [Category.assoc, algebraicClosureBaseChangeIso_hom_naturality,
      Iso.inv_hom_id_assoc] at h
    exact h
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hgeom
    (hi.1.isClosedSubgroup.baseChange b)

/-- Arbitrary field extension reflects the geometric Borel condition of an
actual closed inclusion into an affine group. -/
theorem IsGeometricBorelSubgroup.of_baseChange_field [IsAffineHom G.X.hom]
    (hi : IsGeometricBorelSubgroup
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i) : IsGeometricBorelSubgroup i := by
  let a := toAlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c := toAlgebraicClosure K
  let d := algebraicClosureBaseMap k K
  let e := algebraicClosureBaseChangeIso k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  let : IsAffineHom ((baseChange a).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom a))
  have hbar : IsBorelSubgroup ((baseChange d).map ((baseChange a).map i)) := by
    have h := (hi.2.iso_comp (e.app B)).comp_iso (e.app G).symm
    change IsBorelSubgroup (((e.app B).hom ≫
      (baseChange c).map ((baseChange b).map i)) ≫ (e.app G).inv) at h
    rw [← algebraicClosureBaseChangeIso_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at h
    exact h
  have hb : IsBorelSubgroup ((baseChange a).map i) :=
    IsBorelSubgroup.of_baseChange_of_isAlgClosed hbar (hclosed.baseChange a)
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hb hclosed

/-- The geometric Borel condition of a closed inclusion in a connected
reductive group is unchanged by arbitrary field extension. -/
theorem isGeometricBorelSubgroup_baseChange_field_iff
    (hG : IsConnectedReductive G) (hclosed : IsClosedSubgroup i) :
    IsGeometricBorelSubgroup
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) ↔
      IsGeometricBorelSubgroup i := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact ⟨fun hi => hi.of_baseChange_field hclosed,
    fun hi => hi.baseChange_field hG⟩

end Fields

end Langlands.GroupScheme
