/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyTriangleLaws
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import all WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Mathlib.CategoryTheory.Presentable.Directed

/-! # Continuity for a supplied fixed-base cohomology cocone

Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ), and Tag 0032.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- The canonical cocone of fixed-base cohomology is a colimit. This asserts only the
universal property for supplied diagram and cocone data; it does not construct them.
Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ), and Tag 0032.
(blueprint: lem-weil-pbc-cofiltered-fixed-base-cohomology-continuity)

Proof:
1. Choose a small nonempty directed partial order A and a final functor A to J opposite
   by the cofiltered limit directed reindexing lemma (Stacks 0032). Its opposite is
   initial, so whiskering c gives a limit cone with the same point. The reindexed
   schemes are qcqs and their transition maps are affine by the given instances.
2. At a stage take the inverse image of G along the structure map to S. The inverse
   of upperStarComp gives the sheaf transition map, using naturality of pi. The
   unit and associativity coherence of inverse-image composition give its identity
   and composition laws. The hypotheses hH identify the reindexed H with its
   canonical cohomology diagram.
3. On the limit use the constant diagram with value t inverse image G. The equations
   ht and upperStarComp identify this diagram with the pulled-back stage sheaves.
   Associativity coherence gives compatibility of these identifications with the
   transitions. A nonempty directed category is connected, so the identity cocone
   on this constant diagram is a colimit of the limit sheaves.
4. Apply nonempty_isColimit_etale_cohomology_of_isLimit (Stacks 09YQ) to this reindexed
   system and this constant sheaf colimit. Its specified comparison legs are exactly
   the right sides of hB. Thus the whiskering of B is a colimit cocone.
5. Finality reflects the colimit universal property of B, giving the result on J
   opposite. The isomorphisms eH and eB only transport objects and do not change this
   property. Neither the source theorem nor this argument requires torsion.

Edge cases: the index is nonempty by cofilteredness; the one-object case reduces to
an isomorphism cocone. Zero sheaves, empty schemes and degree zero require no changes.
-/
theorem nonempty_isColimit_cofiltered_fixed_base_cohomology
    {J : Type u} [SmallCategory J] [IsCofiltered J] {S : Scheme.{u}}
    (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (t : c.pt ⟶ S)
    (ht : ∀ j : J, t = c.π.app j ≫ π.app j)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (H : Jᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ j : J, H.obj (op j) ≅
      AddCommGrpCat.of (Sheaf.H (((π.app j)^*[AddCommGrpCat.{u + 1}]).obj G) q))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f.op =
      (eH k).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (D.map f) (π.app k) (π.app j)
          (by
            have h := (π.naturality f).symm
            change π.app j ≫ 𝟙 S = D.map f ≫ π.app k at h
            exact (Category.comp_id _).symm.trans h) G q) ≫ (eH j).inv)
    (B : Cocone H)
    (eB : B.pt ≅ AddCommGrpCat.of
      (Sheaf.H (((t)^*[AddCommGrpCat.{u + 1}]).obj G) q))
    (hB : ∀ j : J, B.ι.app (op j) ≫ eB.hom =
      (eH j).hom ≫ AddCommGrpCat.ofHom
        (cohomologyTriangleMap (c.π.app j) (π.app j) t (ht j) G q)) :
    Nonempty (IsColimit B) := by
  obtain ⟨I, hI, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Jᵒᵖ
  let D' := R.leftOp ⋙ D
  let (i : Iᵒᵖ) : CompactSpace (D'.obj i) := inferInstanceAs
    (CompactSpace (D.obj (R.obj i.unop).unop))
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D'.obj i) := inferInstanceAs
    (QuasiSeparatedSpace (D.obj (R.obj i.unop).unop))
  let (i j : Iᵒᵖ) (f : i ⟶ j) : IsAffineHom (D'.map f) := inferInstanceAs
    (IsAffineHom (D.map (R.map f.unop).unop))
  let c' := c.whisker R.leftOp
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv R.leftOp c).symm hc
  let v := fun i : I ↦ π.app (R.obj i).unop
  have wv : ∀ (i j : I) (f : i ⟶ j), v j = D'.map f.op ≫ v i := by
    intro i j f
    simp [v, D']
  have wLimit : ∀ i : I, t = c'.π.app (op i) ≫ v i := fun i ↦ ht (R.obj i).unop
  let H' := R ⋙ H
  let B' := B.whisker R
  suffices h : Nonempty (IsColimit B') from
    h.map (Functor.Final.isColimitWhiskerEquiv R B)
  set_option backward.isDefEq.respectTransparency true in
    apply continuity_constant_pullback D' c' hc' S G v wv t wLimit q H'
      (fun i ↦ eH (R.obj i).unop) ?_ B' eB ?_
    · intro i j f
      simpa only [H', D', v, cohomologyTriangleMap, AddCommGrpCat.ofHom_comp,
        Category.assoc, Functor.comp_map, Functor.leftOp_map, Quiver.Hom.op_unop,
        Functor.comp_obj, Opposite.op_unop]
        using hH (R.obj j).unop (R.obj i).unop (R.map f).unop
    · intro i
      simpa only [B', c', v, cohomologyTriangleMap, AddCommGrpCat.ofHom_comp,
        Category.assoc, Cocone.whisker_ι, Cone.whisker_π, Opposite.op_unop,
        Functor.whiskerLeft_app, Functor.leftOp_obj]
        using hB (R.obj i).unop

end AlgebraicGeometry.Etale
