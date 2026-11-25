/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLiftAffine
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLiftLocalFamily

/-! # An intermediate step in continuity of étale sections
Source: Stacks Project, Tag 09YQ. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem sectionComparison_naturality
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1)))
    {U V : R.Etale} (a : V ⟶ U) :
    ((Scheme.etaleSetPullback f).obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map a).op ≫
      etaleSetSectionComparison h f k hk G V =
    etaleSetSectionComparison h f k hk G U ≫
      ((Scheme.etaleSetPullback k).obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ k).map a).op := by
  let F := (Scheme.etaleSetPullback f).obj G
  let H := (Scheme.etaleSetPullback k).obj G
  let pb := MorphismProperty.Over.pullback @Etale ⊤ f
  let ph := MorphismProperty.Over.pullback @Etale ⊤ h
  let pk := MorphismProperty.Over.pullback @Etale ⊤ k
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    ph (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app F).hom
  let e := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G
  let q := eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk)
  let r := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).hom
  have hη := η.naturality ((pb.map a).op)
  have he := e.hom.naturality ((ph.map (pb.map a)).op)
  have hq := q.hom.naturality ((ph.map (pb.map a)).op)
  have hr := r.naturality a
  change F.obj.map (pb.map a).op ≫ η.app (op (pb.obj V)) ≫
      e.hom.app (op (ph.obj (pb.obj V))) ≫ q.hom.app (op (ph.obj (pb.obj V))) ≫
      H.obj.map (r.app V).op =
    η.app (op (pb.obj U)) ≫ e.hom.app (op (ph.obj (pb.obj U))) ≫
      q.hom.app (op (ph.obj (pb.obj U))) ≫ H.obj.map (r.app U).op ≫
      H.obj.map (pk.map a).op
  erw [reassoc_of% hη, reassoc_of% he, reassoc_of% hq]
  apply congrArg (fun z ↦ η.app (op (pb.obj U)) ≫
    e.hom.app (op (ph.obj (pb.obj U))) ≫ q.hom.app (op (ph.obj (pb.obj U))) ≫ z)
  change H.obj.map (ph.map (pb.map a)).op ≫ H.obj.map (r.app V).op =
    H.obj.map (r.app U).op ≫ H.obj.map (pk.map a).op
  rw [← H.obj.map_comp, ← H.obj.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun z ↦ H.obj.map z.op) hr.symm


/-- Source: Stacks Project, Étale Cohomology, Theorem Tag 09YQ, proof via Tags 0EYL,
04HR, and 09YN, followed by finite affine-cover descent.
(blueprint: lem-weil-pbc-sets-section-lift).
Proof: restrict to the cofinal tail of the chosen stage. For affine W₀, affine transition
maps and limit projections allow the affine-site inverse-image comparison. The affine
site colimit and restriction equivalences identify limit sections with the filtered
colimit of stage sections, by the colimit-of-sites section theorem. The composition
isomorphisms identify the pulled-back sheaves at the limit with the constant sheaf
system having value the inverse image of G there; connectedness identifies its colimit
with that inverse image. Unit compatibility identifies its maps with the displayed
comparisons, so every section lifts to a stage.
For general W₀, choose a finite affine cover and finite affine refinements of its overlaps.
Lift the restrictions of t on this finite cover by the affine result. The overlap
equalities hold at the limit; etaleSetSectionEventualEquality makes them hold at some
later stage. Directedness supplies one common stage for all lifts and equalities.
The sheaf equalizer condition glues these compatible lifts to a section of W at that
stage. Uniqueness in the sheaf condition identifies its limit image with t. Empty
covers give the unique section of the empty object, so include that case. -/
theorem etaleSetSectionLift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))) :
    ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀))),
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W₀) s = t := by
  classical
  have haff : ∀ (W : (D.obj (op i₀)).Etale) (_ : IsAffine W.left),
      QuasiCompact W.hom → QuasiSeparated W.hom →
      ∀ t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W)),
      ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W))),
        (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W) s = t := by
    intro W hW hqc hqs t'
    exact etaleSetSectionLift_affine D c hc i₀ G W t'
  obtain ⟨n, V, f, j, s, _, hcover, hlimit, hcompatible, hs⟩ :=
    etaleSetSectionLift_local_family D c hc i₀ G W₀ haff t
  let F := (Scheme.etaleSetPullback (D.map j.hom)).obj G
  let H := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
  let pb := MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
  let pk := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
  let x (b : Fin n) : PUnit.{u + 2} ⟶ F.obj.obj (op (pb.obj (V b))) :=
    TypeCat.ofHom (fun _ ↦ s b)
  have hx : ∀ ⦃Y : (D.obj j.left).Etale⦄ ⦃b b' : Fin n⦄
      (a : Y ⟶ pb.obj (V b)) (a' : Y ⟶ pb.obj (V b')),
      a ≫ pb.map (f b) = a' ≫ pb.map (f b') →
        x b ≫ F.obj.map a.op = x b' ≫ F.obj.map a'.op := by
    intro Y b b' a a' h
    ext z
    exact hcompatible Y b b' a a' h
  obtain ⟨y, hy, _⟩ :=
    F.property.existsUnique_amalgamation_ofArrows (fun b ↦ pb.map (f b)) hcover x hx
  refine ⟨j, y PUnit.unit, ?_⟩
  let q := etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
    (c.π.app (op i₀)) (c.w j.hom) G W₀
  let qt : PUnit.{u + 2} ⟶ H.obj.obj (op (pk.obj W₀)) := TypeCat.ofHom (fun _ ↦ t)
  have he : y ≫ q = qt := by
    apply H.property.hom_ext_ofArrows (fun b ↦ pk.map (f b)) hlimit
    intro b
    have hn := sectionComparison_naturality (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) G (f b)
    change y ≫ q ≫ H.obj.map (pk.map (f b)).op = qt ≫ H.obj.map (pk.map (f b)).op
    rw [← hn, ← Category.assoc, hy b]
    ext z
    exact hs b
  exact congrArg (fun a ↦ a PUnit.unit) he

end AlgebraicGeometry
