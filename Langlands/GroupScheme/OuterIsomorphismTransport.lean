import Langlands.GroupScheme.OuterIsomorphismScheme

/-! # Transport of supplied isomorphism schemes and outer quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A B : GroupScheme S}
  (I J : GroupIsomorphismScheme G H)

/-- The canonical comparison between two representatives of the same isomorphism functor. -/
def representativeHom : I.parameter ⟶ J.parameter :=
  J.classify I.universalIso

/-- The representative comparison preserves the universal isomorphism on every test. -/
theorem representativeHom_eval {T : Over S} (p : T ⟶ I.parameter)
    (g : T ⟶ G.X) :
    J.universalIso.toFun (p ≫ I.representativeHom J) g =
      I.universalIso.toFun p g := by
  exact congrArg (fun e : LocalGroupIso G H I.parameter => e.toFun p g)
    (J.refine_classify I.universalIso)

/-- Two schemes representing the same all-test isomorphism functor are canonically isomorphic. -/
def representativeIso : I.parameter ≅ J.parameter where
  hom := I.representativeHom J
  inv := J.representativeHom I
  hom_inv_id := by
    apply I.hom_ext
    intro W t g
    simp only [← Category.assoc, representativeHom_eval, Category.comp_id]
  inv_hom_id := by
    apply J.hom_ext
    intro W t g
    simp only [← Category.assoc, representativeHom_eval, Category.comp_id]

/-- The canonical representative comparison intertwines inverse-precomposition actions. -/
theorem representativeIso_equivariant (a : AutomorphicAction A G)
    {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter) :
    (lift d p ≫ I.actionHom a) ≫ (I.representativeIso J).hom =
      lift d (p ≫ (I.representativeIso J).hom) ≫ J.actionHom a := by
  apply J.hom_ext
  intro W t g
  change J.universalIso.toFun
      (t ≫ ((lift d p ≫ I.actionHom a) ≫ I.representativeHom J)) g =
    J.universalIso.toFun
      (t ≫ (lift d (p ≫ I.representativeHom J) ≫ J.actionHom a)) g
  simp only [← Category.assoc, comp_lift, representativeHom_eval,
    actionHom_eval]

/-- Replacing the acting group by an isomorphic group preserves the canonical action. -/
theorem actionHom_changeActingGroup (a : AutomorphicAction A G)
    (b : AutomorphicAction B G) (e : B ≅ A)
    (he : ∀ (T : Over S) (d : T ⟶ B.X) (g : T ⟶ G.X),
      b.act d g = a.act (d ≫ e.hom.hom.hom) g)
    {T : Over S} (d : T ⟶ B.X) (p : T ⟶ I.parameter) :
    lift d p ≫ I.actionHom b =
      lift (d ≫ e.hom.hom.hom) p ≫ I.actionHom a := by
  apply I.hom_ext
  intro W t g
  simp only [← Category.assoc, comp_lift, actionHom_eval, he,
    GrpObj.inv_comp]

end GroupIsomorphismScheme

namespace OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A B : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a)

/-- Transport an outer quotient along the canonical equivariant isomorphism of
isomorphism-functor representatives. -/
def changeRepresentative (J : GroupIsomorphismScheme G H) :
    OuterIsomorphismScheme J a where
  parameter := O.parameter
  classMap := (J.representativeIso I).hom ≫ O.classMap
  flat := by
    have : IsIso (J.representativeIso I).hom.left :=
      (Over.forget S).map_isIso _
    change Flat ((J.representativeIso I).hom.left ≫ O.classMap.left)
    infer_instance
  surjective := by
    have : IsIso (J.representativeIso I).hom.left :=
      (Over.forget S).map_isIso _
    change Surjective ((J.representativeIso I).hom.left ≫ O.classMap.left)
    infer_instance
  quasiCompact := by
    have : IsIso (J.representativeIso I).hom.left :=
      (Over.forget S).map_isIso _
    change QuasiCompact ((J.representativeIso I).hom.left ≫ O.classMap.left)
    infer_instance
  invariant T d p := by
    rw [← Category.assoc, J.representativeIso_equivariant I a,
      O.invariant, Category.assoc]
  orbit T p q hpq := by
    obtain ⟨d, hd, hu⟩ := O.orbit T
      (p ≫ (J.representativeIso I).hom) (q ≫ (J.representativeIso I).hom)
      (by simpa only [Category.assoc] using hpq)
    have hj (c : T ⟶ A.X) :
        lift c p ≫ J.actionHom a = q ↔
          lift c (p ≫ (J.representativeIso I).hom) ≫ I.actionHom a =
            q ≫ (J.representativeIso I).hom := by
      rw [← J.representativeIso_equivariant I a]
      exact ⟨fun h => congrArg (fun z => z ≫ (J.representativeIso I).hom) h,
        fun h => (cancel_mono (J.representativeIso I).hom).mp h⟩
    exact ⟨d, (hj d).mpr hd, fun c hc => hu c ((hj c).mp hc)⟩

/-- Reindex an outer quotient by an isomorphic acting group with the same action. -/
def changeActingGroup (b : AutomorphicAction B G) (e : B ≅ A)
    (he : ∀ (T : Over S) (d : T ⟶ B.X) (g : T ⟶ G.X),
      b.act d g = a.act (d ≫ e.hom.hom.hom) g) :
    OuterIsomorphismScheme I b where
  parameter := O.parameter
  classMap := O.classMap
  flat := O.flat
  surjective := O.surjective
  quasiCompact := O.quasiCompact
  invariant T d p := by
    rw [I.actionHom_changeActingGroup a b e he, O.invariant]
  orbit T p q hpq := by
    obtain ⟨d, hd, hu⟩ := O.orbit T p q hpq
    let c : T ⟶ B.X := d ≫ e.inv.hom.hom
    have hc : c ≫ e.hom.hom.hom = d := by
      change (d ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = d
      rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id]
    refine ⟨c, ?_, ?_⟩
    · change lift c p ≫ I.actionHom b = q
      rw [I.actionHom_changeActingGroup a b e he, hc]
      exact hd
    · intro c' hc'
      have hc'd : c' ≫ e.hom.hom.hom = d := by
        apply hu
        rw [← I.actionHom_changeActingGroup a b e he]
        exact hc'
      have : IsIso e.hom.hom.hom :=
        (Grp.forget (Over S)).map_isIso e.hom
      apply (cancel_mono e.hom.hom.hom).mp
      exact hc'd.trans hc.symm

end OuterIsomorphismScheme

end Langlands.GroupScheme
