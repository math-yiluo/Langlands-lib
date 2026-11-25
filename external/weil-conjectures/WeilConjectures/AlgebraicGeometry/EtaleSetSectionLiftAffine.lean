/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetStageSheafColimit
import WeilConjectures.AlgebraicGeometry.AffineSectionsColimit
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonNaturality

/-! # Affine stage lifting of étale inverse-image sections
Source: Stacks Project, Étale Cohomology, Tag 09YQ, using Sites Tag 09YN. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] etaleSetSectionComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Constructing the sheaf diagram involves several nested functor compositions.
/-- Source: Stacks Project, Étale Cohomology Tag 09YQ, proof via Tags 0EYL,
04HR and Sites Tag 09YN (blueprint: lem-weil-pbc-sets-section-lift-affine).
Proof: on the original full affine étale site, construct the stage push-pull sheaves
and their comparison maps. Restriction naturality makes these maps sheaf morphisms;
the comparison laws give the diagram identities and the cone compatibility.
The sheaf-level continuity bridge identifies this explicit cocone as a colimit.
The finite-cover evaluation theorem then makes its sections on W₀ a colimit of sets.
The type-colimit representative theorem supplies a stage section mapping to t;
the explicitly defined cocone leg is the required etaleSetSectionComparison.
The empty affine scheme causes no exception: its section set is a singleton by the
sheaf condition and the filtered tail is nonempty. -/
theorem etaleSetSectionLift_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [IsAffine W₀.left]
    [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))) :
    ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀))),
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W₀) s = t := by
  classical
  let ρ := (Scheme.fullAffineEtaleInclusion (D.obj (op i₀))).sheafPushforwardContinuous
    (Type (u + 1)) (Scheme.fullAffineEtaleTopology (D.obj (op i₀)))
    (D.obj (op i₀)).smallEtaleTopology
  let A (j : Over (op i₀)) := ρ.obj
    (((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).sheafPushforwardContinuous
      (Type (u + 1)) ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
      ((D.obj j.left).smallGrothendieckTopology @Etale)).obj
        ((Scheme.etaleSetPullback (D.map j.hom)).obj G))
  let L := ρ.obj
    ((@Functor.sheafPushforwardContinuous _ _ _ _
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))) (Type (u + 1)) _
      ((D.obj (op i₀)).smallGrothendieckTopology @Etale)
      (c.pt.smallGrothendieckTopology @Etale)
      (Etale.isContinuous_overPullback (c.π.app (op i₀)))).obj
        ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G))
  let r {j k : Over (op i₀)} (a : k ⟶ j) : A j ⟶ A k :=
    ⟨{ app W := etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
        ((D.map_comp a.left j.hom).symm.trans
          (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W.unop.obj
       naturality W V f := by
        exact (etaleSetSectionComparison_naturality (D.map a.left) (D.map j.hom) (D.map k.hom)
          ((D.map_comp a.left j.hom).symm.trans
            (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G f.unop.hom).symm }⟩
  let q (j : Over (op i₀)) : A j ⟶ L :=
    ⟨{ app W := etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G W.unop.obj
       naturality W V f := by
        exact (etaleSetSectionComparison_naturality (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G f.unop.hom).symm }⟩
  let E : (Over (op i₀))ᵒᵖ ⥤
      Sheaf (Scheme.fullAffineEtaleTopology (D.obj (op i₀))) (Type (u + 1)) :=
    { obj j := A j.unop
      map a := r a.unop
      map_id j := by
        ext W x
        simpa [r, A, ρ, Functor.sheafPushforwardContinuous,
          Scheme.fullAffineEtaleInclusion] using
          ConcreteCategory.congr_hom
            ((etaleSetSectionComparisonLaws D c i₀ G W.unop.obj).1 j.unop) x
      map_comp a b := by
        ext W x
        simpa [r, A, ρ, Functor.sheafPushforwardContinuous,
          Scheme.fullAffineEtaleInclusion] using
          ConcreteCategory.congr_hom (((etaleSetSectionComparisonLaws D c i₀ G W.unop.obj).2.1
          _ _ _ a.unop b.unop).symm) x }
  let K : Cocone E :=
    { pt := L
      ι :=
        { app j := q j.unop
          naturality j k a := by
            ext W x
            simpa [q, r, E, L, A, ρ, Functor.sheafPushforwardContinuous,
              Scheme.fullAffineEtaleInclusion] using
              ConcreteCategory.congr_hom (((etaleSetSectionComparisonLaws D c i₀ G W.unop.obj).2.2
              _ _ a.unop).trans (Category.comp_id _).symm) x } }
  obtain ⟨hK⟩ := etaleSetStageSheaf_isColimit D c hc i₀ G E K
    (fun _ ↦ rfl) rfl (fun _ _ _ _ ↦ rfl) (fun _ _ ↦ rfl)
  let W : (D.obj (op i₀)).FullAffineEtale := ⟨W₀, inferInstance⟩
  obtain ⟨hsections⟩ := affineSections_colimit E K hK W
  obtain ⟨j, s, hs⟩ := Types.jointly_surjective_of_isColimit hsections t
  exact ⟨j.unop, s, hs⟩

end AlgebraicGeometry
