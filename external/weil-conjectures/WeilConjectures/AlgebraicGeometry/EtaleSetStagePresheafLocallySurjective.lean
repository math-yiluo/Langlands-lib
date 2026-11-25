/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.EtaleSetFiniteLocalStageRepresentatives
import WeilConjectures.AlgebraicGeometry.EtaleSetEventualLocalStageMatching

/-! # Local surjective comparison with the stage presheaf colimit

Source: Stacks Project, Sites Tag 0A35 and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-stage-presheaf-locally-surjective).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem glue_stage_representatives
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (H M : Sheaf J (Type (u + 1))) (φ : H ⟶ M) {Y : C}
    {n : ℕ} (V : Fin n → C) (a : ∀ q, V q ⟶ Y)
    (s : ∀ q, H.obj.obj (op (V q))) (t : M.obj.obj (op Y))
    (ha : Sieve.ofArrows V a ∈ J Y)
    (hs : ∀ q, φ.hom.app (op (V q)) (s q) = M.obj.map (a q).op t)
    (hm : Presieve.Arrows.Compatible H.obj a s) :
    ∃ x : H.obj.obj (op Y), φ.hom.app (op Y) x = t := by
  have hH := Presieve.IsSheaf.isSheafFor
    ((isSheaf_iff_isSheaf_of_type J _).1 H.property) (Presieve.ofArrows V a) ha
  obtain ⟨x, hx, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hH s hm
  refine ⟨x, ?_⟩
  have hM := Presieve.IsSheaf.isSheafFor
    ((isSheaf_iff_isSheaf_of_type J _).1 M.property) (Presieve.ofArrows V a) ha
  apply hM.isSeparatedFor.ext
  rintro Z f ⟨q⟩
  rw [← NatTrans.naturality_apply φ.hom (a q).op x, hx q, hs q]

private theorem range_of_arrow_eq
    {X Y X' Y' : Type (u + 1)} (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : Arrow.mk f = Arrow.mk g) (hY : Y = Y') (t : Y)
    (s : X') (hs : g s = (eqToHom hY) t) : ∃ x : X, f x = t := by
  obtain ⟨hX, hY', hf⟩ := (Arrow.mk_eq_mk_iff f g).1 h
  subst X'
  subst Y'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst g
  exact ⟨s, by simpa using hs⟩

set_option backward.isDefEq.respectTransparency false in
private theorem stage_global_representative
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).FullAffineEtale)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))) :
    ∃ (j : Over (op i₀))
      (x : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W.obj))),
      etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G W.obj x = t := by
  obtain ⟨j, n, V, a, s, ha, hV, hs⟩ :=
    etaleSet_finiteLocalStageRepresentatives D c hc i₀ G W t
  obtain ⟨j', r, hcov, himg, hmatch⟩ :=
    etaleSet_eventualLocalStageMatching D c hc i₀ G W t j n V a s ha hV hs
  let b := MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)
  let hr := (D.map_comp r.left j.hom).symm.trans
    (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
  let d := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (D.map r.left) (D.map j.hom) (D.map j'.hom) hr.symm).app W.obj
  let V' := fun q ↦ b.obj (V q)
  let a' := fun q ↦ b.map (a q) ≫ d.inv
  let s' := fun q ↦ (etaleSetSheafComparison (D.map r.left) (D.map j.hom)
    (D.map j'.hom) hr G).hom.app (op (V q)) (s q)
  let H := (Scheme.etaleSetPullback (D.map j'.hom)).obj G
  let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
  let B := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j'.left)
  let Y := (MorphismProperty.Over.pullback @Etale ⊤ (D.map j'.hom)).obj W.obj
  let e := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (c.π.app j'.left) (D.map j'.hom) (c.π.app (op i₀)) (c.w j'.hom).symm).app W.obj
  let β := etaleSetSheafComparison (c.π.app j'.left) (D.map j'.hom)
    (c.π.app (op i₀)) (c.w j'.hom) G
  let : B.IsContinuous ((D.obj j'.left).smallGrothendieckTopology @Etale)
      (c.pt.smallGrothendieckTopology @Etale) :=
    Etale.isContinuous_overPullback (c.π.app j'.left)
  let M := (B.sheafPushforwardContinuous (Type (u + 1))
    ((D.obj j'.left).smallGrothendieckTopology @Etale)
    (c.pt.smallGrothendieckTopology @Etale)).obj L
  have hlocal : ∀ q, β.hom.app (op (V' q)) (s' q) =
      M.obj.map (a' q).op (L.obj.map e.inv.op t) := by
    intro q
    change β.hom.app (op (V' q)) (s' q) =
      L.obj.map (B.map (a' q)).op (L.obj.map e.inv.op t)
    have hi := himg q
    change β.hom.app (op (V' q)) (s' q) =
      L.obj.map (B.map (a' q) ≫ e.inv).op t at hi
    rw [op_comp, L.obj.map_comp, ConcreteCategory.comp_apply] at hi
    exact hi
  -- Compare in the pushforward sheaf on the same stage cover used for gluing.
  obtain ⟨x, hx⟩ := glue_stage_representatives H M β V' a' s'
    (L.obj.map e.inv.op t) hcov hlocal hmatch
  refine ⟨j', x, ?_⟩
  change L.obj.map e.hom.op (β.hom.app (op Y) x) = t
  change β.hom.app (op Y) x = L.obj.map e.inv.op t at hx
  rw [hx]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Iso.hom_inv_id, op_id]
  exact ConcreteCategory.congr_hom (L.obj.map_id _) t

/-- The comparison from the presheaf colimit to the limit push-pull sheaf
is locally surjective.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit,
and Étale Cohomology Tag 09YQ, via the affine-site colimit presentation.
(blueprint: lem-weil-pbc-sets-stage-presheaf-locally-surjective).

Proof: 1. Restrict the system to the cofinal upper tail of i₀. Apply the affine
   étale site colimit presentation to this tail. The base change of an affine
   test object W is affine, because the cone projection is affine. Transport
   the stage and limit inverse images through the full-affine restriction
   equivalences using the unit-compatible inverse-image comparison.
2. The construction in Sites 0A35, equation-compute-pullback-to-limit,
   represents a limit inverse-image section by stage inverse-image sections.
   Indeed inverse-image sections are locally represented by an original
   section of G and a map into its base change. The finite-presentation object
   and arrow descent clauses place these maps at stages. A covering that
   supplies these representatives has a finite affine refinement; descend
   that finite cover to a common stage using covering descent.
3. Overlaps of the local representatives agree at the limit. Descend the
   finite equations witnessing agreement to a later common stage, using the
   eventual-equality clause of the site presentation. The sheaf axiom at
   that stage glues the representatives. This is the existence part of
   0A35's section formula. The adjunction-unit and composition equations
   identify its map with etaleSetSectionComparison and hence, by the supplied
   component equations, with the leg of K.
4. Insert the resulting stage representative into the presheaf colimit
   using its coprojection. The presheaf colimit universal property says that
   its comparison image is the given limit section. Thus the image sieve is
   covering (indeed the argument gives a representative on W itself).
   Empty covers are allowed throughout; on an empty object the sheaf axiom
   gives the unique section, with no nonemptiness assumption on G. -/
theorem etaleSetStagePresheaf_locallySurjective
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1))) :
    let ρ := (Scheme.fullAffineEtaleInclusion (D.obj (op i₀))).sheafPushforwardContinuous
      (Type (u + 1)) (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
      (D.obj (op i₀)).smallEtaleTopology
    let A := fun j : Over (op i₀) ↦ ρ.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).sheafPushforwardContinuous
        (Type (u + 1)) ((D.obj (op i₀)).smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        ((D.obj j.left).smallGrothendieckTopology (P := @Etale) (Q := @Etale))).obj
          ((Scheme.etaleSetPullback (D.map j.hom)).obj G))
    let L := ρ.obj
      ((@Functor.sheafPushforwardContinuous _ _ _ _
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀)))
        (Type (u + 1)) _ ((D.obj (op i₀)).smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        (c.pt.smallGrothendieckTopology (P := @Etale) (Q := @Etale))
        (Etale.isContinuous_overPullback (c.π.app (op i₀)))).obj
          ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G))
    ∀ (E : (Over (op i₀))ᵒᵖ ⥤
        Sheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀))) (Type (u + 1)))
      (K : Cocone E),
      (∀ j : Over (op i₀), E.obj (op j) = A j) → K.pt = L →
      (∀ (j k : Over (op i₀)) (a : k ⟶ j)
        (W : (D.obj (op i₀)).FullAffineEtale),
        Arrow.mk ((E.map a.op).hom.app (op W)) =
          Arrow.mk (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp a.left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W.obj)) →
      (∀ (j : Over (op i₀)) (W : (D.obj (op i₀)).FullAffineEtale),
        Arrow.mk ((K.ι.app (op j)).hom.app (op W)) =
          Arrow.mk (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
            (c.π.app (op i₀)) (c.w j.hom) G W.obj)) →
      Presheaf.IsLocallySurjective
      (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
      (colimit.desc
        (E ⋙ sheafToPresheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
          (Type (u + 1)))
        ((sheafToPresheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
          (Type (u + 1))).mapCocone K)) := by
  dsimp only
  intro E K _hE hK _hmap hι
  apply Presheaf.isLocallySurjective_of_surjective
  intro W t
  let hY := congrArg (fun S ↦ S.obj.obj W) hK
  obtain ⟨j, s, hs⟩ := stage_global_representative D c hc i₀ G W.unop ((eqToHom hY) t)
  obtain ⟨x, hx⟩ := range_of_arrow_eq ((K.ι.app (op j)).hom.app W)
    (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) G W.unop.obj)
    (hι j W.unop) hY t s hs
  refine ⟨(colimit.ι (E ⋙ sheafToPresheaf _ (Type (u + 1))) (op j)).app W x, ?_⟩
  have he := NatTrans.congr_app
    (colimit.ι_desc ((sheafToPresheaf _ (Type (u + 1))).mapCocone K) (op j)) W
  exact (ConcreteCategory.congr_hom he x).trans hx

end AlgebraicGeometry
