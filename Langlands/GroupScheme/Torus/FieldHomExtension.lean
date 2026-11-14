import Langlands.GroupScheme.Torus.ExponentHomomorphisms

/-! # Extending field-fibre homomorphisms between split tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {k : Type u} [Field k]
  (b : Spec (CommRingCat.of k) ⟶ S) {T T' : CommGroupScheme S}

/-- Every homomorphism between field fibres of two split tori extends to
an actual homomorphism over their original base. -/
theorem IsSplitTorus.hom_fieldBaseChange_surjective
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) :
    Function.Surjective
      (fun f : T ⟶ T' => (CommGroupScheme.baseChange b).map f) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  obtain ⟨J, hJ, ⟨e'⟩⟩ := hT'
  let := hI
  let := hJ
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let eC : T ≅ splitTorus.commGroupScheme S I := CommGroupScheme.isoOfGroupIso e
  let eC' : T' ≅ splitTorus.commGroupScheme S J := CommGroupScheme.isoOfGroupIso e'
  let B := CommGroupScheme.baseChange b
  let d := splitTorus.commBaseChangeIso b I
  let d' := splitTorus.commBaseChangeIso b J
  let q := B.mapIso eC ≪≫ d
  let q' := B.mapIso eC' ≪≫ d'
  intro f
  let c := q.inv ≫ f ≫ q'.hom
  let c₀ := splitTorus.exponentHom S I J
    (splitTorus.characterMap I J (CommGroupScheme.groupHom c))
  refine ⟨eC.hom ≫ c₀ ≫ eC'.inv, ?_⟩
  have hc : d.inv ≫ B.map c₀ ≫ d'.hom = c := by
    rw [← splitTorus.exponentHom_baseChange S I J b, Iso.inv_hom_id_assoc]
    exact splitTorus.exponentHom_characterMap k I J (CommGroupScheme.groupHom c)
  have hc' : B.map c₀ = d.hom ≫ c ≫ d'.inv := by
    rw [← hc]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change B.map (eC.hom ≫ c₀ ≫ eC'.inv) = f
  rw [Functor.map_comp, Functor.map_comp, hc']
  dsimp only [c, q, q', Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [B.map_id, Category.id_comp, ← B.map_comp, eC'.hom_inv_id,
    B.map_id, Category.comp_id]

/-- A chosen extension of a specified actual field-fibre homomorphism. -/
def IsSplitTorus.fieldHomExtension
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (f : (CommGroupScheme.baseChange b).obj T ⟶
      (CommGroupScheme.baseChange b).obj T') : T ⟶ T' :=
  Classical.choose (hT.hom_fieldBaseChange_surjective b hT' f)

@[simp] theorem IsSplitTorus.fieldHomExtension_baseChange
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (f : (CommGroupScheme.baseChange b).obj T ⟶
      (CommGroupScheme.baseChange b).obj T') :
    (CommGroupScheme.baseChange b).map (hT.fieldHomExtension b hT' f) = f :=
  Classical.choose_spec (hT.hom_fieldBaseChange_surjective b hT' f)

end Langlands.GroupScheme
