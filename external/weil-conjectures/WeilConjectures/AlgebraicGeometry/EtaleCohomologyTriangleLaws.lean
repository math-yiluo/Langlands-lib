/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Cohomology maps for commuting triangles over a fixed base

Source: Stacks Project, Cohomology, Section 20.14 (Tag 01F7).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- Pullback along a commuting triangle, followed by the inverse-image comparison.
Source: Stacks Project, Tag 01F7. 
(blueprint: lem-weil-pbc-etale-cohomology-triangle-laws)
-/
noncomputable def cohomologyTriangleMap {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Y ⟶ S) (b : X ⟶ S) (h : b = f ≫ a)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H (((a)^*[AddCommGrpCat.{u + 1}]).obj G) q →+
      Sheaf.H (((b)^*[AddCommGrpCat.{u + 1}]).obj G) q :=
  (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f a b h).inv.app G) q).comp
    (cohomologyMap f (((a)^*[AddCommGrpCat.{u + 1}]).obj G) q)

/-- A triangle map carries restriction from the base to restriction from the base.
Source: Stacks Project, Tag 01F7. 
(blueprint: lem-weil-pbc-etale-cohomology-triangle-laws)
-/
theorem cohomologyTriangleMap_restriction {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Y ⟶ S) (b : X ⟶ S) (h : b = f ≫ a)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H G q) :
    cohomologyTriangleMap f a b h G q (cohomologyMap a G q x) =
      cohomologyMap b G q x := by
  subst b
  unfold cohomologyTriangleMap
  dsimp only [AddMonoidHom.comp_apply]
  have hcomp := (cohomologyPullbackFunctorial f a G q).2.1 x
  change cohomologyMap f (((a)^*[AddCommGrpCat.{u + 1}]).obj G) q
    (cohomologyMap a G q x) = _ at hcomp
  calc
    _ = Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f a).inv.app G) q
        (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f a).hom.app G) q
          (cohomologyMap (f ≫ a) G q x)) := congrArg _ hcomp
    _ = _ := by rw [← Sheaf.H.map_comp_apply]; simp

/-- Triangle maps are unital and compose contravariantly over a fixed base.
Source: Stacks Project, Cohomology, Section 20.14 (Tag 01F7).
(blueprint: lem-weil-pbc-etale-cohomology-triangle-laws)

Proof:
1. For the identity triangle, the inverse-image comparison is the identity comparison
   whiskered with pullback along a. The identity part of cohomology pullback functoriality
   therefore gives the identity map on H^q(a inverse image G).
2. For X --f--> Y --g--> Z over S, apply naturality of cohomological pullback to the
   inverse-image comparison for g and the structure map of Z. Apply composition of
   cohomological pullback to f and g. The two resulting sheaf morphisms agree by the
   associativity coherence of inverse-image composition: they are the same comparison
   between left adjoints to the threefold direct-image composite, compatible with units.
3. Functoriality of H^q on sheaf morphisms and cancellation of each composition
   isomorphism with its inverse give the displayed equality. Equality proofs in the
   triangle data do not affect the maps by proof irrelevance. This argument applies to
   every scheme and sheaf, without compactness, torsion, or index assumptions.
-/
theorem cohomologyTriangleMap_laws
    (S : Scheme.{u}) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ (X : Scheme.{u}) (a : X ⟶ S),
      cohomologyTriangleMap (𝟙 X) a a (by simp) G q = AddMonoidHom.id _) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (a : Z ⟶ S) (b : Y ⟶ S) (d : X ⟶ S)
      (hb : b = g ≫ a) (hd : d = f ≫ b),
      cohomologyTriangleMap (f ≫ g) a d (by rw [hd, hb, Category.assoc]) G q =
        (cohomologyTriangleMap f b d hd G q).comp
          (cohomologyTriangleMap g a b hb G q)) := by
  constructor
  · intro X a
    ext x
    unfold cohomologyTriangleMap
    dsimp only [AddMonoidHom.id_apply, AddMonoidHom.comp_apply]
    rw [upperStarComp_id_left]
    simpa using (cohomologyPullbackFunctorial (𝟙 X) (𝟙 X)
      (((a)^*[AddCommGrpCat.{u + 1}]).obj G) q).2.2 x
  · intro X Y Z f g a b d hb hd
    subst b
    subst d
    ext x
    unfold cohomologyTriangleMap
    dsimp only [AddMonoidHom.comp_apply]
    let F := (((a)^*[AddCommGrpCat.{u + 1}]).obj G)
    let α := (upperStarComp AddCommGrpCat.{u + 1} g a).inv.app G
    let β := (upperStarComp AddCommGrpCat.{u + 1} f (g ≫ a)).inv.app G
    have hn := cohomologyMap_map f q α (cohomologyMap g F q x)
    have hc := (cohomologyPullbackFunctorial f g F q).2.1 x
    symm
    calc
      _ = Sheaf.H.map β q
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map α) q
            (cohomologyMap f (((g)^*[AddCommGrpCat.{u + 1}]).obj F) q
              (cohomologyMap g F q x))) := congrArg (Sheaf.H.map β q) hn
      _ = Sheaf.H.map β q
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map α) q
            (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f g).hom.app F) q
              (cohomologyMap (f ≫ g) F q x))) :=
        congrArg (fun y ↦ Sheaf.H.map β q
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map α) q y)) hc
      _ = _ := by
        dsimp [α, β, F]
        rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
        rw [upperStarComp_hom_app_map_upperStarComp_inv_app_assoc
          AddCommGrpCat.{u + 1} f g a (f ≫ g) (g ≫ a) (f ≫ g ≫ a)
          rfl rfl (Category.assoc f g a) G]
        simp only [Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Etale
