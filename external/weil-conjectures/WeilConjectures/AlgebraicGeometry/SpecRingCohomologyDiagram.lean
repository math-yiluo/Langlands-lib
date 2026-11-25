/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyTriangleLaws

/-! # The canonical cohomology diagram of a ring system

Source: Stacks Project, Tags 09YQ.
(blueprint: lem-weil-pbc-spec-ring-cohomology-diagram)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Compatible maps from spectra of a ring diagram determine a cohomology diagram
and a cocone with the canonical pullback legs. No continuity assertion is made here.

Source: Stacks Project, Tag 09YQ, the cohomology diagram and comparison map.
(blueprint: lem-weil-pbc-spec-ring-cohomology-diagram)

Proof: Set H(a) to the cohomology of the inverse image of G along v(a).
For f : a to b, pull cohomology back along Spec(R(f)) and then apply the inverse
of the inverse-image composition isomorphism, using the given equation wv.
Naturality of pullback on cohomology and the composition coherence of inverse
image show that these maps compose. The identity coherence gives the identity
law. For the cocone vertex take the cohomology of the inverse image along vLimit.
Define the leg at a by pullback along Spec(c.ι(a)) followed by the inverse
composition isomorphism for wLimit(a). The cocone identity for c and the same
composition coherence prove naturality of these legs. Take eH and eB to be
identity isomorphisms. This construction does not use the colimit property of c,
filteredness, henselianness, or torsion; these are needed only by subsequent
continuity applications. It works for the zero ring and in degree zero. -/
theorem exists_spec_ring_cohomology_diagram
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, Spec (R.obj i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = Spec.map (R.map f) ≫ v i)
    (vLimit : Spec c.pt ⟶ T) (wLimit : ∀ i : I, vLimit = Spec.map (c.ι.app i) ≫ v i)
    (p : ℕ) :
    ∃ (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p)),
    (∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (R.map f))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (R.map f)) (v i)
            (v j) (wv i j f)).inv.app G) p) ≫ (eH j).inv) ∧
    ∃ (B : Cocone H) (eB : B.pt ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} vLimit).obj G) p)),
    (∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (c.ι.app i))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (c.ι.app i)) (v i)
            vLimit (wLimit i)).inv.app G) p)) := by
  have _ := hc
  have laws := cohomologyTriangleMap_laws T G p
  let D : Iᵒᵖ ⥤ Scheme.{u} := R.op ⋙ Scheme.Spec
  let d : Cone D := Scheme.Spec.mapCone c.op
  let H : I ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun i ↦ AddCommGrpCat.of
        (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p)
      map := fun {i j} f ↦ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (D.map f.op) (v i) (v j) (wv i j f) G p)
      map_id := by
        intro i
        change AddCommGrpCat.ofHom
          (cohomologyTriangleMap (D.map (𝟙 (.op i))) (v i) (v i) _ G p) = 𝟙 _
        simp only [D.map_id]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.1 (D.obj (.op i)) (v i))).trans AddCommGrpCat.ofHom_id
      map_comp := by
        intro i j k f g
        change AddCommGrpCat.ofHom
          (cohomologyTriangleMap (D.map (g.op ≫ f.op)) (v i) (v k) _ G p) =
            AddCommGrpCat.ofHom
              (cohomologyTriangleMap (D.map f.op) (v i) (v j) _ G p) ≫
            AddCommGrpCat.ofHom
              (cohomologyTriangleMap (D.map g.op) (v j) (v k) _ G p)
        simp only [D.map_comp]
        exact (congrArg AddCommGrpCat.ofHom
          (laws.2 (D.obj (.op k)) (D.obj (.op j)) (D.obj (.op i))
            (D.map g.op) (D.map f.op) (v i) (v j) (v k)
            (wv i j f) (wv j k g))).trans (AddCommGrpCat.ofHom_comp _ _) }
  let B : Cocone H :=
    { pt := AddCommGrpCat.of
        (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} vLimit).obj G) p)
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom
            (cohomologyTriangleMap (d.π.app (.op i)) (v i) vLimit (wLimit i) G p)
          naturality := by
            intro i j f
            change AddCommGrpCat.ofHom
              (cohomologyTriangleMap (D.map f.op) (v i) (v j) _ G p) ≫
              AddCommGrpCat.ofHom
                (cohomologyTriangleMap (d.π.app (.op j)) (v j) vLimit _ G p) =
              AddCommGrpCat.ofHom
                (cohomologyTriangleMap (d.π.app (.op i)) (v i) vLimit _ G p) ≫ 𝟙 _
            simp only [Category.comp_id]
            have h := laws.2 d.pt (D.obj (.op j)) (D.obj (.op i))
              (d.π.app (.op j)) (D.map f.op) (v i) (v j)
              vLimit (wv i j f) (wLimit j)
            simp only [d.w f.op] at h
            exact (AddCommGrpCat.ofHom_comp _ _).symm.trans
              (congrArg AddCommGrpCat.ofHom h).symm } }
  refine ⟨H, fun _ ↦ Iso.refl _, ?_, B, Iso.refl _, ?_⟩
  · intro i j f
    change AddCommGrpCat.ofHom (cohomologyTriangleMap
      (Spec.map (R.map f)) (v i) (v j) (wv i j f) G p) =
        𝟙 _ ≫ _ ≫ _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact AddCommGrpCat.ofHom_comp _ _
  · intro i
    change AddCommGrpCat.ofHom (cohomologyTriangleMap
      (Spec.map (c.ι.app i)) (v i) vLimit (wLimit i) G p) ≫ 𝟙 _ = 𝟙 _ ≫ _ ≫ _
    simp only [Category.id_comp, Category.comp_id]
    exact AddCommGrpCat.ofHom_comp _ _


end AlgebraicGeometry.Etale
