import Langlands.GroupScheme.Torus.HenselianNormalizerLifting

/-! # Extending an isomorphism of field fibres of two split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

variable (k : Type u) [Field k] (I J : Type u)
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Extend a field isomorphism between standard split tori of possibly
different index types by its actual integral character maps. -/
def fieldCommIsoExtension (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J) :
    commGroupScheme S I ≅ commGroupScheme S J where
  hom := exponentHom S I J (characterMap I J c.hom)
  inv := exponentHom S J I (characterMap J I c.inv)
  hom_inv_id := by
    rw [exponentHom_comp, ← characterMap_comp, c.hom_inv_id,
      characterMap_id, exponentHom_id]
  inv_hom_id := by
    rw [exponentHom_comp, ← characterMap_comp, c.inv_hom_id,
      characterMap_id, exponentHom_id]

/-- Pullback recovers the specified actual field isomorphism on its hom map. -/
theorem fieldCommIsoExtension_baseChange (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J)
    (b : Spec (CommRingCat.of k) ⟶ S) :
    (commBaseChangeIso b I).inv ≫
        (CommGroupScheme.baseChange b).map (fieldCommIsoExtension k I J S c).hom ≫
        (commBaseChangeIso b J).hom = Additive.ofMul c.hom := by
  change (commBaseChangeIso b I).inv ≫
    (CommGroupScheme.baseChange b).map (exponentHom S I J (characterMap I J c.hom)) ≫
    (commBaseChangeIso b J).hom = _
  rw [← exponentHom_baseChange, Iso.inv_hom_id_assoc]
  exact exponentHom_characterMap k I J c.hom

end splitTorus

variable {S : Scheme.{u}} {k : Type u} [Field k]
  (b : Spec (CommRingCat.of k) ⟶ S) {T T' : CommGroupScheme S}

/-- Every specified field-fibre isomorphism of two split tori extends over
their original arbitrary base, with exact recovery of that isomorphism. -/
theorem IsSplitTorus.iso_fieldBaseChange_surjective
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) :
    Function.Surjective
      (fun e : T ≅ T' => (CommGroupScheme.baseChange b).mapIso e) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  obtain ⟨J, hJ, ⟨e'⟩⟩ := hT'
  let := hI
  let := hJ
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let eC : T ≅ splitTorus.commGroupScheme S I :=
    CommGroupScheme.isoOfGroupIso e
  let eC' : T' ≅ splitTorus.commGroupScheme S J :=
    CommGroupScheme.isoOfGroupIso e'
  let B := CommGroupScheme.baseChange b
  let d := splitTorus.commBaseChangeIso b I
  let d' := splitTorus.commBaseChangeIso b J
  let q := B.mapIso eC ≪≫ d
  let q' := B.mapIso eC' ≪≫ d'
  intro σ
  let c := q.symm ≪≫ σ ≪≫ q'
  let cG : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J :=
    { hom := CommGroupScheme.groupHom c.hom
      inv := CommGroupScheme.groupHom c.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom c.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom c.inv_hom_id }
  let c₀ := splitTorus.fieldCommIsoExtension k I J S cG
  refine ⟨eC ≪≫ c₀ ≪≫ eC'.symm, ?_⟩
  apply Iso.ext
  change B.map (eC.hom ≫ c₀.hom ≫ eC'.inv) = σ.hom
  have hc : d.inv ≫ B.map c₀.hom ≫ d'.hom = c.hom :=
    splitTorus.fieldCommIsoExtension_baseChange k I J S cG b
  have hc' : B.map c₀.hom = d.hom ≫ c.hom ≫ d'.inv := by
    rw [← hc]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, hc']
  dsimp only [c, q, q', Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [B.map_id, Category.id_comp, ← B.map_comp, eC'.hom_inv_id,
    B.map_id, Category.comp_id]

end Langlands.GroupScheme
