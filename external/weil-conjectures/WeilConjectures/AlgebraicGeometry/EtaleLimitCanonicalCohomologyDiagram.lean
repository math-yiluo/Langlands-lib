/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Canonical comparison diagrams for etale cohomology

Source: Stacks Project, Tags 01F7 and 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem functor_transport_map
    {α C D : Type*} [Category C] [Category D]
    (P : α → C ⥤ D) (K : D ⥤ AddCommGrpCat.{u + 1}) (F : C) {A : Type*}
    (m : ∀ a, A → K.obj ((P a).obj F)) (a b : α) (h : a = b) (x : A) :
    K.map ((eqToIso (congrArg P h)).hom.app F) (m a x) = m b x := by
  subst b
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_identity_transport {X : Scheme.{u}} (f : X ⟶ X)
    (hf : f = 𝟙 X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map
      ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app F ≫
        (upperStarId AddCommGrpCat.{u + 1} X).hom.app F) n
      (cohomologyMap f F n x) = x := by
  rw [Sheaf.H.map_comp_apply]
  have ht := functor_transport_map (upperStar AddCommGrpCat.{u + 1})
    (Sheaf.functorH X.smallEtaleTopology n) F
    (fun f x ↦ cohomologyMap f F n x) f (𝟙 X) hf x
  change Sheaf.H.map
    ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app F) n
    (cohomologyMap f F n x) = cohomologyMap (𝟙 X) F n x at ht
  exact (congrArg (Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) n)
    ht).trans ((cohomologyPullbackFunctorial (𝟙 X) (𝟙 X) F n).2.2 x)

set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_composition_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hh : h = f ≫ g)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f g h hh).hom.app F) n
      (cohomologyMap h F n x) =
        cohomologyMap f ((upperStar AddCommGrpCat.{u + 1} g).obj F) n
          (cohomologyMap g F n x) := by
  subst h
  exact ((cohomologyPullbackFunctorial f g F n).2.1 x).symm

-- The existential witness `hH` is intentionally unused in the following conclusion.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Cohomology functoriality constructs the canonical comparison diagram in any degree.

Source: Stacks Project, Tags 01F7 and 09YQ (canonical comparison map).
(blueprint: lem-weil-pbc-etale-limit-canonical-cohomology-diagram).

Proof: Put H_i = H^n(F_i) and take its arrows to be cohomology pullback followed
by the map of the coefficient transition. The identity and composition equations
for the coefficient system, pullback functoriality and naturality prove the functor
laws. Put B.pt = H^n(L.pt) and take each leg to be pullback along the cone projection
followed by the cohomology map of the colimit leg, after the given identification eG.
The cone equation, pullback composition, coefficient naturality and naturality of
L.ι prove the cocone equation. All object identifications are identity isomorphisms.
This works for arbitrary degree and arbitrary cocone L; no exactness, vanishing,
continuity, or connecting map enters the construction. In particular it includes
zero and empty-scheme cohomology groups and does not require an index initial object.
-/
theorem etale_limit_canonical_cohomology_diagram
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (n : ℕ) :
    ∃ (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) n))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) n) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt n))
    , ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) n) := by
  let H : I ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun i ↦ AddCommGrpCat.of (Sheaf.H (F i) n)
      map := fun {i j} f ↦ AddCommGrpCat.ofHom
        ((Sheaf.H.map (φ f) n).comp (cohomologyMap (D.map f.op) (F i) n))
      map_id := by
        intro i
        ext x
        dsimp only [AddCommGrpCat.ofHom_apply, AddMonoidHom.comp_apply,
          AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply]
        rw [hidentity]
        exact cohomology_identity_transport _ (D.map_id (op i)) (F i) n x
      map_comp := by
        intro i j k f g
        ext x
        change Sheaf.H.map (φ (f ≫ g)) n
          (cohomologyMap (D.map (f ≫ g).op) (F i) n x) =
          Sheaf.H.map (φ g) n (cohomologyMap (D.map g.op) (F j) n
            (Sheaf.H.map (φ f) n (cohomologyMap (D.map f.op) (F i) n x)))
        rw [hcomposition, Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
        exact (congrArg (fun y ↦ Sheaf.H.map (φ g) n
          (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f)) n y))
          (cohomology_composition_transport (D.map g.op) (D.map f.op)
            (D.map (f ≫ g).op) (D.map_comp g.op f.op) (F i) n x)).trans
          (congrArg (Sheaf.H.map (φ g) n)
            (cohomologyMap_map (D.map g.op) n (φ f)
              (cohomologyMap (D.map f.op) (F i) n x)).symm) }
  let B : Cocone H :=
    { pt := AddCommGrpCat.of (Sheaf.H L.pt n)
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom
            ((Sheaf.H.map ((eG i).inv ≫ L.ι.app i) n).comp
              (cohomologyMap (c.π.app (op i)) (F i) n))
          naturality := by
            intro i j f
            ext x
            change Sheaf.H.map ((eG j).inv ≫ L.ι.app j) n
              (cohomologyMap (c.π.app (op j)) (F j) n
                (Sheaf.H.map (φ f) n (cohomologyMap (D.map f.op) (F i) n x))) =
              Sheaf.H.map ((eG i).inv ≫ L.ι.app i) n
                (cohomologyMap (c.π.app (op i)) (F i) n x)
            have ht :
                (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
                  (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
                (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫
                ((eG j).inv ≫ L.ι.app j) = (eG i).inv ≫ L.ι.app i := by
              have h := congrArg (fun t ↦ (eG i).inv ≫ t) (L.w f)
              simpa only [hG, Category.assoc, Iso.inv_hom_id_assoc] using h
            rw [cohomologyMap_map]
            rw [← cohomology_composition_transport (c.π.app (op j)) (D.map f.op)
              (c.π.app (op i)) (c.w f.op).symm (F i) n x]
            rw [← Sheaf.H.map_comp_apply
              ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f))
              ((eG j).inv ≫ L.ι.app j)]
            exact (Sheaf.H.map_comp_apply
              ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
                (c.π.app (op i)) (c.w f.op).symm).hom.app (F i))
              ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫
                ((eG j).inv ≫ L.ι.app j))
              (cohomologyMap (c.π.app (op i)) (F i) n x)).symm.trans
                (congrArg (fun t ↦ Sheaf.H.map t n
                  (cohomologyMap (c.π.app (op i)) (F i) n x)) ht) } }
  refine ⟨H, fun _ ↦ Iso.refl _, ?_, B, Iso.refl _, ?_⟩
  · intro i j f
    simp only [H, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact AddCommGrpCat.ofHom_comp _ _
  · intro i
    simp only [B, Iso.refl_hom, Category.id_comp]
    exact AddCommGrpCat.ofHom_comp _ _

end AlgebraicGeometry.Etale
