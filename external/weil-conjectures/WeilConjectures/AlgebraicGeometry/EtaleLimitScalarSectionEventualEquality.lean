/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleAbelianSectionColimitEventualEquality
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageUnitEventualEquality
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionPullbackCompatibility
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionMapLaws

/-! # Eventual equality of descended scalar sections

Source: Stacks Project, Sites Tag 09YN and Etale Cohomology Tag 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Equality of two stage sections in the limit is detected at a later stage.
Source: Stacks Project, Sites Tag 09YN, lemma-colimit, the iterated-colimit
argument; Etale Cohomology Tags 0EYL and 09YQ, affine-site realization.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-eventual-equality).

Proof: Restrict the scheme system to the directed upper tail of i₀. Its limit
is unchanged. Base change T₀ and choose a finite affine open cover of T₀.
Affine transition maps preserve the affineness of these base changes. The
projection equations determine γ and δ by the two pullback projections.
On each affine member, present the limit affine etale site as the colimit of
stage sites (0EYL), and transport the sheaves along the full affine etale
restriction equivalences. For each stage sheaf the inverse-image presentation
of 09YM computes its sections at the limit object by later-stage sections.
The finite-cover section theorem computes the sections of the sheaf colimit
L as the filtered colimit of the sections of the inverse images. Insert the
09YM presentations into this latter colimit. A finite collection of descended
objects, arrows, and equalities has a common refinement; thus the refinement
category is filtered and the diagonal system is final. Flattening the two
colimits identifies the two equal images with equal representatives in the
stage-section colimit. Its equality relation gives a later equality witness.
The inverse-image unit equations, hG, and the projection equations identify
these maps with μ and ρ. There are finitely many affine cover members, so
choose one stage above all these witnesses. The transition sections agree on
a covering at that stage, hence agree by the separatedness of the stage sheaf.
This proves only equality detection; it supplies no representative of an
arbitrary limit section and does not assume scalar colimit universality.
For the empty object separatedness for the empty cover gives the conclusion
at the original stage; zero coefficients and a singleton index also cause no
exception. No object is defined by choosing a section witness. -/
theorem etale_limit_scalar_sections_eventual_equality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    (L : Cocone G) (hL : IsColimit L)
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale)
    [CompactSpace T₀.left] [QuasiSeparatedSpace T₀.left] :
    let J := {j : I // i₀ ≤ j}
    let Tj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj T₀
    let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j) ≅ Tj k)
      (δ : ∀ j : J,
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j.val))).obj (Tj j) ≅ Tlim),
      (∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫ pullback.fst T₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Tj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
      (∀ j : J,
        (δ j).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀)) =
          pullback.fst (Tj j).hom (c.π.app (op j.val)) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
    let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
    let μ := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (L.ι.app j.val).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        L.pt.obj.map (δ j).inv.op
    ∀ (j : J) (s t : (F j.val).obj.obj (op (Tj j))), μ j s = μ j t →
      ∃ (k : J) (a : j ⟶ k), ρ j k a s = ρ j k a t := by
  dsimp only
  intro γ δ hγ hδ
  have : CompactSpace ↥((𝟭 Scheme).obj T₀.left) :=
    inferInstanceAs (CompactSpace T₀.left)
  have : QuasiSeparatedSpace ↥((𝟭 Scheme).obj T₀.left) :=
    inferInstanceAs (QuasiSeparatedSpace T₀.left)
  let J := {j : I // i₀ ≤ j}
  let Tj := fun j : J ↦
    (MorphismProperty.Over.pullback @Etale ⊤
      (D.map (homOfLE j.property).op)).obj T₀
  let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
  let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
  let ν := fun j : J ↦
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
      (eG j.val).inv.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Tj j))) ≫
      (G.obj j.val).obj.map (δ j).inv.op
  intro j s t hst
  have hmu (x : (F j.val).obj.obj (op (Tj j))) :
      (ν j ≫ (L.ι.app j.val).hom.app (op Tlim)) x =
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
          (eG j.val).inv.hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤
              (c.π.app (op j.val))).obj (Tj j))) ≫
          (L.ι.app j.val).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤
              (c.π.app (op j.val))).obj (Tj j))) ≫
          L.pt.obj.map (δ j).inv.op) x := by
    have hn := (L.ι.app j.val).hom.naturality (δ j).inv.op
    dsimp only [ν]
    rw [Category.assoc, Category.assoc, hn]
    rfl
  have hcol : (L.ι.app j.val).hom.app (op Tlim) (ν j s) =
      (L.ι.app j.val).hom.app (op Tlim) (ν j t) :=
    (hmu s).trans (hst.trans (hmu t).symm)
  have : ∀ {i k : Iᵒᵖ} (f : i ⟶ k), IsAffineHom (D.map f) :=
    fun {_ _} _ ↦ inferInstance
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc (op i₀)
  have : CompactSpace Tlim.left := by
    change CompactSpace ↥(pullback T₀.hom (c.π.app (op i₀)))
    exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst T₀.hom (c.π.app (op i₀)))
  obtain ⟨k₀, a₀, ha₀⟩ :=
    etale_abelian_section_colimit_eventual_equality c.pt Tlim G L hL j.val
      (ν j s) (ν j t) hcol
  let k : J := ⟨k₀, j.property.trans (leOfHom a₀)⟩
  let a : j ⟶ k := homOfLE (leOfHom a₀)
  have hν := etale_limit_scalar_section_pullback_compatibility
    D c F φ G eG hG i₀ T₀ γ δ hγ hδ
  have hunit_norm : ν k (ρ j k a s) = ν k (ρ j k a t) := by
    have hs := ConcreteCategory.congr_hom (hν j k a) s
    have ht := ConcreteCategory.congr_hom (hν j k a) t
    exact hs.symm.trans (ha₀.trans ht)
  have hunit :
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op k.val))).unit.app (F k.val)).hom.app (op (Tj k)) (ρ j k a s) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op k.val))).unit.app (F k.val)).hom.app (op (Tj k)) (ρ j k a t) := by
    have : IsIso ((eG k.val).inv.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op k.val))).obj (Tj k)))) := inferInstance
    have : IsIso ((G.obj k.val).obj.map (δ k).inv.op) := inferInstance
    apply (ConcreteCategory.bijective_of_isIso
      ((eG k.val).inv.hom.app _)).1
    apply (ConcreteCategory.bijective_of_isIso ((G.obj k.val).obj.map (δ k).inv.op)).1
    exact hunit_norm
  have : CompactSpace (Tj k).left := by
    change CompactSpace ↥(pullback T₀.hom (D.map (homOfLE k.property).op))
    exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst T₀.hom (D.map (homOfLE k.property).op))
  have : QuasiSeparatedSpace (Tj k).left := by
    change QuasiSeparatedSpace ↥(pullback T₀.hom (D.map (homOfLE k.property).op))
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst T₀.hom (D.map (homOfLE k.property).op))
  obtain ⟨l₀, b₀, hb₀⟩ := etale_inverse_image_unit_eventual_equality
    D c hc k.val (F k.val) (Tj k) (ρ j k a s) (ρ j k a t) hunit
  let l : J := ⟨l₀, k.property.trans (leOfHom b₀)⟩
  let b : k ⟶ l := homOfLE (leOfHom b₀)
  have hstage : ρ k l b (ρ j k a s) = ρ k l b (ρ j k a t) := by
    exact congrArg (fun x ↦
      ((φ b₀).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map b₀.op)).obj (Tj k))) ≫
        (F l.val).obj.map (γ k l b).inv.op) x) hb₀
  obtain ⟨_, hcomp, _⟩ := etale_limit_scalar_section_map_laws
    D c F φ hidentity hcomposition G eG hG L i₀ T₀ γ δ hγ hδ
  refine ⟨l, a ≫ b, ?_⟩
  exact (ConcreteCategory.congr_hom (hcomp j k l a b) s).trans
    (hstage.trans (ConcreteCategory.congr_hom (hcomp j k l a b) t).symm)


end AlgebraicGeometry.Etale
