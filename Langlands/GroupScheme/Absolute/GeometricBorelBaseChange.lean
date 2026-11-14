import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Descent.QuasiSplitDatum
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.GeometricConnectedness

/-! # Preservation and reflection of geometric Borel subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Projection from the field pullback of the chosen geometric-point test
scheme, viewed over the original field. -/
def geometricPointPullbackProjection {k K : Type u} [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    (Over.map b).obj ((Over.pullback b).obj
      ((Over.map (toAlgebraicClosure k)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))))) ⟶
    (Over.map (toAlgebraicClosure k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) :=
  Over.homMk (pullback.fst _ b) pullback.condition

section SolvabilityReflection

variable {k K : Type u} [Field k] [Field K]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Solvability of a smooth affine pullback reflects along a flat surjective
map of field spectra. -/
theorem IsSolvableGroupScheme.of_baseChange
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [Flat b] [Surjective b]
    (hsm : Smooth ((GroupScheme.baseChange b).obj G).X.hom)
    (haff : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom)
    (hsol : IsSolvableGroupScheme ((GroupScheme.baseChange b).obj G)) :
    IsSolvableGroupScheme G := by
  let H := (GroupScheme.baseChange b).obj G
  let : IsAffineHom H.X.hom := haff
  let T := (Over.map (toAlgebraicClosure k)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
  let V := (Over.pullback b).obj T
  let q : (Over.map b).obj V ⟶ T := geometricPointPullbackProjection b
  let : Epi q.left := by
    change Epi (pullback.fst T.hom b)
    exact Flat.epi_of_flat_of_surjective _
  let : Epi q := Over.epi_of_epi_left q
  let e := baseChangePointsEquiv b G V
  let : Group.IsSolvable (V ⟶ H.X) :=
    SolvableFieldExtensionProof.allPoints_isSolvable H hsm hsol V
  let : Group.IsSolvable ((Over.map b).obj V ⟶ G.X) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let f : (T ⟶ G.X) →* ((Over.map b).obj V ⟶ G.X) :=
    { toFun := fun x => q ≫ x
      map_one' := MonObj.comp_one q
      map_mul' := fun x y => MonObj.comp_mul q x y }
  let : Group.IsSolvable (T ⟶ G.X) :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      (fun x y h => (cancel_epi q).mp h)
  let c := baseChangePointsEquiv (toAlgebraicClosure k) G
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
  exact Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective

end SolvabilityReflection

section Reflection

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {B G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {i : B ⟶ G}

/-- A closed inclusion is Borel if it becomes Borel after a field extension. -/
theorem IsBorelSubgroup.of_baseChange
    (hi : IsBorelSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i) : IsBorelSubgroup i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := GroupScheme.baseChange b
  obtain ⟨hp, hf, hq⟩ := fieldExtension_fpqc k K
  let : Surjective b := hp
  let : Flat b := hf
  let : QuasiCompact b := hq
  let : IsAffineHom B.X.hom := hclosed.isAffineHom
  have haff : IsAffineHom (F.obj B).X.hom := by
    change IsAffineHom (pullback.snd B.X.hom b)
    infer_instance
  refine ⟨hclosed, smooth_of_baseChange b B hi.smooth,
    connectedSpace_of_baseChange b B hi.connectedSpace,
    IsSolvableGroupScheme.of_baseChange b hi.smooth haff hi.isSolvableGroupScheme, ?_⟩
  intro C j f hj hsm hconn hsol hfac
  let : IsAffineHom C.X.hom := hj.isAffineHom
  let : Smooth C.X.hom := hsm
  let : ConnectedSpace C.X.left := hconn
  have : IsIso (F.map f) := hi.maximal (F.obj C) (F.map j) (F.map f)
    (hj.baseChange b)
    (show Smooth (pullback.snd C.X.hom b) from inferInstance)
    (C.connectedSpace_baseChange_of_smooth_affine b)
    (solvableFieldExtensionStatement k K b C hsm hsol)
    (by rw [← F.map_comp, hfac])
  exact isIso_of_baseChange b f

/-- A closed inclusion is geometric Borel if it becomes geometric Borel
after any field extension. -/
theorem IsGeometricBorelSubgroup.of_baseChange
    (hi : IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i) : IsGeometricBorelSubgroup i := by
  let a := toAlgebraicClosure k
  let c := algebraicClosureBaseMap k K
  let e := algebraicClosureBaseChangeIso k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  have hn := e.hom.naturality i
  change (GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i) ≫
    (e.app G).hom = (e.app B).hom ≫
      (GroupScheme.baseChange (toAlgebraicClosure K)).map
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)
    at hn
  have h := (hi.2.iso_comp (e.app B)).comp_iso (e.app G).symm
  change IsBorelSubgroup
    (((e.app B).hom ≫
      (GroupScheme.baseChange (toAlgebraicClosure K)).map
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)) ≫
      (e.app G).inv) at h
  rw [← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  let : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom a)
    infer_instance
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
    (IsBorelSubgroup.of_baseChange
      (k := AlgebraicClosure k) (K := AlgebraicClosure K) h (hclosed.baseChange a))
    hclosed

end Reflection

section Preservation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {B G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {i : B ⟶ G}

/-- Geometric Borels in smooth connected affine groups remain geometric
Borel under every field extension. -/
theorem IsGeometricBorelSubgroup.baseChange_of_smooth_affine
    (hi : IsGeometricBorelSubgroup i) :
    IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  let a := toAlgebraicClosure k
  let c := algebraicClosureBaseMap k K
  let e := algebraicClosureBaseChangeIso k K
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  have hsm : Smooth ((GroupScheme.baseChange a).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom a)
    infer_instance
  have haff : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom a)
    infer_instance
  have hconn : ConnectedSpace ((GroupScheme.baseChange a).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine a
  have hb := borelAlgClosedFieldExtensionStatement
    (AlgebraicClosure k) (AlgebraicClosure K)
    ((GroupScheme.baseChange a).obj G) haff hsm hconn
    ((GroupScheme.baseChange a).obj B) ((GroupScheme.baseChange a).map i) hi.2
  have h := (hb.iso_comp (e.app B).symm).comp_iso (e.app G)
  have hn := e.hom.naturality i
  change (GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i) ≫
    (e.app G).hom = (e.app B).hom ≫
      (GroupScheme.baseChange (toAlgebraicClosure K)).map
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)
    at hn
  change IsBorelSubgroup
    (((e.app B).inv ≫
      (GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i)) ≫
      (e.app G).hom) at h
  rw [Category.assoc, hn, Iso.inv_hom_id_assoc] at h
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure h
    (hi.1.isClosedSubgroup.baseChange b)

end Preservation

end Langlands.GroupScheme

section IntegratedCompanion

/-! # Geometric Borel subgroups under arbitrary field extension -/



open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]
  {B G : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G}

/-- An arbitrary field extension preserves a geometric Borel subgroup of a
connected reductive group, with its actual base-changed inclusion. -/
theorem IsGeometricBorelSubgroup.baseChange
    (hi : IsGeometricBorelSubgroup i) (hG : IsConnectedReductive G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    IsGeometricBorelSubgroup ((GroupScheme.baseChange b).map i) := by
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k K)) = b :=
    Spec.map_preimage b
  rw [← hb]
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  let e := algebraicClosureBaseChangeIso k K
  have hAffine : IsAffineHom
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have hSmooth : Smooth
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have h := borelAlgClosedFieldExtensionStatement
    (AlgebraicClosure k) (AlgebraicClosure K)
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
    hAffine hSmooth hG.connectedSpace_toAlgebraicClosure
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj B)
    ((GroupScheme.baseChange (toAlgebraicClosure k)).map i) hi.2
  have hn := e.hom.naturality i
  have hgeo : IsBorelSubgroup
      ((GroupScheme.baseChange (toAlgebraicClosure K)).map
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)) := by
    have ht := (h.iso_comp (e.app B).symm).comp_iso (e.app G)
    change IsBorelSubgroup
      (((e.app B).inv ≫
        (GroupScheme.baseChange (algebraicClosureBaseMap k K)).map
          ((GroupScheme.baseChange (toAlgebraicClosure k)).map i)) ≫
            (e.app G).hom) at ht
    change
      (GroupScheme.baseChange (algebraicClosureBaseMap k K)).map
          ((GroupScheme.baseChange (toAlgebraicClosure k)).map i) ≫ (e.app G).hom =
        (e.app B).hom ≫
          (GroupScheme.baseChange (toAlgebraicClosure K)).map
            ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) at hn
    rwa [Category.assoc, hn, Iso.inv_hom_id_assoc] at ht
  have : IsAffineHom
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom _)
    infer_instance
  exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hgeo
    (hi.1.isClosedSubgroup.baseChange _)

end Langlands.GroupScheme

end IntegratedCompanion
