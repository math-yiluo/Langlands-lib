import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Descent.QuasiSplitDatum
import Langlands.GroupScheme.GeometricConnectedness

/-! # Geometric Borel subgroups under arbitrary field extension -/

noncomputable section

universe u

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
