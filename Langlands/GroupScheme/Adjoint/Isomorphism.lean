import Langlands.GroupScheme.Adjoint.InnerAction

/-! # Isomorphisms induced on supplied adjoint quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsAdjointQuotient

variable {k : Type u} [Field k]
    {G H A B : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} {p : H ⟶ B}
    (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)

include hp in
/-- Transporting a source isomorphism and then taking the target quotient kills
all points of the source's full scheme-theoretic centre. -/
theorem killsCenter_iso_comp (e : G ≅ H) : KillsCenter (e.hom ≫ p) := by
  intro T x hx
  change (x ≫ e.hom.hom.hom) ≫ p.hom.hom = 1
  exact hp.killsCenter T _ (mem_center_comp_iso e hx)

/-- An actual isomorphism induces an actual isomorphism between supplied
full-centre adjoint quotients. -/
def mapIso (e : G ≅ H) : A ≅ B where
  hom := hq.desc (e.hom ≫ p) (hp.killsCenter_iso_comp e)
  inv := hp.desc (e.inv ≫ q) (hq.killsCenter_iso_comp e.symm)
  hom_inv_id := by
    apply hq.hom_ext
    rw [← Category.assoc, hq.comp_desc, Category.assoc, hp.comp_desc,
      ← Category.assoc, e.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply hp.hom_ext
    rw [← Category.assoc, hp.comp_desc, Category.assoc, hq.comp_desc,
      ← Category.assoc, e.inv_hom_id, Category.id_comp, Category.comp_id]

/-- The induced isomorphism commutes with the actual quotient maps. -/
theorem comp_mapIso_hom (e : G ≅ H) :
    q ≫ (hq.mapIso hp e).hom = e.hom ≫ p :=
  hq.comp_desc _ (hp.killsCenter_iso_comp e)

/-- The inverse induced isomorphism also commutes with the quotient maps. -/
theorem comp_mapIso_inv (e : G ≅ H) :
    p ≫ (hq.mapIso hp e).inv = e.inv ≫ q :=
  hp.comp_desc _ (hq.killsCenter_iso_comp e.symm)

/-- The quotient square uniquely determines the induced isomorphism. -/
theorem mapIso_unique (e : G ≅ H) (d : A ≅ B)
    (hd : q ≫ d.hom = e.hom ≫ p) : d = hq.mapIso hp e := by
  apply Iso.ext
  exact hq.hom_ext (hd.trans (hq.comp_mapIso_hom hp e).symm)

/-- The induced quotient map has the same effect on the images of all test points. -/
theorem mapIso_hom_points (e : G ≅ H) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) :
    (g ≫ q.hom.hom) ≫ (hq.mapIso hp e).hom.hom.hom =
      (g ≫ e.hom.hom.hom) ≫ p.hom.hom := by
  have h := congrArg (fun f : G ⟶ B => g ≫ f.hom.hom)
    (hq.comp_mapIso_hom hp e)
  exact h

/-- The induced isomorphism respects inversion of the original isomorphism. -/
theorem mapIso_symm (e : G ≅ H) :
    (hq.mapIso hp e).symm = hp.mapIso hq e.symm := by
  apply hp.mapIso_unique hq e.symm
  exact hq.comp_mapIso_inv hp e

/-- Inner actions commute with the source isomorphism and its induced adjoint
isomorphism on every relative test scheme, without a global lifting premise. -/
theorem mapIso_innerAction (e : G ≅ H) {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ A.X) (g : T ⟶ G.X) :
    hq.innerAction.act x g ≫ e.hom.hom.hom =
      hp.innerAction.act (x ≫ (hq.mapIso hp e).hom.hom.hom)
        (g ≫ e.hom.hom.hom) := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x
  intro V b h hb
  rw [← Category.assoc, hq.innerAction.naturality, hp.innerAction.naturality,
    ← Category.assoc, ← Category.assoc, hb, hq.innerAction_act_lift,
    hq.mapIso_hom_points hp e, hp.innerAction_act_lift]
  simp only [MonObj.mul_comp, GrpObj.inv_comp]

end Langlands.GroupScheme.IsAdjointQuotient
