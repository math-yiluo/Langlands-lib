/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLimitSheafApproximation.AffineLimitSheafApproximation
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteDiagramDescent
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
/-! # The approximation comparison is an epimorphism

Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1.
(blueprint: lem-sc-affine-limit-sheaf-approximation-epi). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem exists_etale_model
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s) (U : s.pt.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    ∃ (i : I) (Ui : (D.obj i).Etale),
      Nonempty ((MorphismProperty.Over.pullback @Etale ⊤ (s.π.app i)).obj Ui ≅ U) := by
  classical
  obtain ⟨J, hJ, hd, hn, G, hG⟩ := IsFiltered.exists_directed Iᵒᵖ
  let := hJ
  let := hd
  let := hn
  let := hG
  let E := G.leftOp ⋙ D
  have (j : Jᵒᵖ) : CompactSpace (E.obj j) :=
    inferInstanceAs (CompactSpace (D.obj (G.leftOp.obj j)))
  have (j : Jᵒᵖ) : QuasiSeparatedSpace (E.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (G.leftOp.obj j)))
  have {j k : Jᵒᵖ} (f : j ⟶ k) : IsAffineHom (E.map f) :=
    inferInstanceAs (IsAffineHom (D.map (G.leftOp.map f)))
  let t := s.whisker G.leftOp
  have ht : IsLimit t := (Functor.Initial.isLimitWhiskerEquiv G.leftOp s).symm hs
  obtain ⟨i, Ui, _, _, e, _, _, _, _⟩ :=
    Etale.exists_etale_limit_finite_diagram_descent E t ht U PEmpty
      (fun k ↦ PEmpty.elim k) (fun k ↦ PEmpty.elim k) (fun k ↦ PEmpty.elim k)
  exact ⟨(G.obj i).unop, Ui, ⟨e⟩⟩

private theorem sheafHom_ext_of_lowerStar
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s)
    {F G : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1}} (a b : F ⟶ G)
    (h : ∀ i, (Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app i)).map a =
      (Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app i)).map b) : a = b := by
  apply Sheaf.hom_ext
  apply (Functor.IsCoverDense.restrictHomEquivHom
    (G := Scheme.AffineEtale.Spec s.pt)).symm.injective
  change Functor.whiskerLeft (Scheme.AffineEtale.Spec s.pt).op a.hom =
    Functor.whiskerLeft (Scheme.AffineEtale.Spec s.pt).op b.hom
  apply NatTrans.ext
  funext U
  change a.hom.app (op ((Scheme.AffineEtale.Spec s.pt).obj U.unop)) =
    b.hom.app (op ((Scheme.AffineEtale.Spec s.pt).obj U.unop))
  have : IsAffine ((Scheme.AffineEtale.Spec s.pt).obj U.unop).left := by
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  obtain ⟨i, Ui, ⟨e⟩⟩ := exists_etale_model D s hs
    ((Scheme.AffineEtale.Spec s.pt).obj U.unop)
  have hi := congrArg (fun k ↦ k.hom.app (op Ui)) (h i)
  apply (cancel_mono (G.obj.map e.hom.op)).mp
  rw [← a.hom.naturality, ← b.hom.naturality]
  exact congrArg (fun k ↦ F.obj.map e.hom.op ≫ k) hi

/-- The counits of the pull-push approximation jointly cover the limit sheaf.
Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1.
(blueprint: lem-sc-affine-limit-sheaf-approximation-epi).

Proof: A final directed reindexing reduces descent of a qcqs étale object to
finite-diagram descent. Affine étale objects therefore descend to stages.
Consequently the direct-image functors along the projections are jointly
faithful: equality can be checked on the affine étale basis, then transported
along a descended object's pullback isomorphism. If two maps agree after the
colimit comparison, they agree after every counit. Applying each adjunction
identifies this with equality of the direct images. Joint faithfulness now
gives equality of the two maps, which is precisely epimorphy. -/
theorem epi_affineLimitSheafApproximationComparison
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s)
    (F : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Epi (Etale.AffineLimitSheafApproximation.approximationComparison D s F) := by
  constructor
  intro G a b hab
  apply sheafHom_ext_of_lowerStar D s hs a b
  intro i
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (s.π.app i)
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  erw [adj.counit.naturality, adj.counit.naturality]
  change adj.counit.app F ≫ a = adj.counit.app F ≫ b
  have he := congrArg
    (fun k ↦ colimit.ι (Etale.AffineLimitSheafApproximation.approximationDiagram D s F)
      (op i) ≫ k) hab
  simpa only [← Category.assoc, Etale.AffineLimitSheafApproximation.approximationComparison,
    colimit.ι_desc, Etale.AffineLimitSheafApproximation.approximationCocone] using he

end AlgebraicGeometry.Scheme
