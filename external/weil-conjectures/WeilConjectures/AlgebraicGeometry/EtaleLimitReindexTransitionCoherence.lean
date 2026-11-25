/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Reindexing coherent inverse-image transition maps -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Work with an abstract pullback functor and its coherence maps so conversion does not
unfold the inverse-image construction. In a preorder the mapped identity and composite
are definitionally equal to the identity and composite of mapped arrows. Equality
witnesses in the coherence maps agree by proof irrelevance. -/
private theorem reindex_transition_coherence_aux
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) →
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (PId : ∀ (X : Scheme.{u}) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (P (𝟙 X)).obj G ⟶ G)
    (PComp : ∀ {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R)
      (fg : T ⟶ R) (_h : fg = f ≫ g)
      (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (P fg).obj G ⟶ (P f).obj ((P g).obj G))
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I) (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (P (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg P (D.map_id (op i)))).hom.app
        (F i) ≫ PId (D.obj (op i)) (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        PComp (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op) (F i) ≫
        (P (D.map g.op)).map (φ f) ≫ φ g)
    :
    let D' := t.op ⋙ D
    let F' (i : J) := F (t.obj i)
    let φ' {i j : J} (f : i ⟶ j) := φ (t.map f)
    ((∀ i : J, φ' (𝟙 i) =
      (eqToIso (congrArg P (D'.map_id (op i)))).hom.app
        (F' i) ≫ PId (D'.obj (op i)) (F' i)) ∧
    (∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      φ' (f ≫ g) =
        PComp (D'.map g.op) (D'.map f.op)
          (D'.map (f ≫ g).op) (D'.map_comp g.op f.op) (F' i) ≫
        (P (D'.map g.op)).map (φ' f) ≫ φ' g))  := by
  constructor
  · intro i
    exact hidentity (t.obj i)
  · intro i j k f g
    exact hcomposition (t.obj i) (t.obj j) (t.obj k) (t.map f) (t.map g)

/-- Inverse-image transition identity and composition are preserved by reindexing.

Source: Stacks Project, Tag 09YQ (theorem-colimit), restriction to a cofinal tail.
(blueprint: lem-weil-pbc-etale-limit-reindex-transition-coherence).

Proof: evaluate the original identity law at t.obj i and the composition law at
 t.map f and t.map g. Functoriality identifies t.map (identity) with identity
and t.map (f composed with g) with t.map f composed with t.map g. The opposite
functor and the composite scheme diagram have the same object and arrow maps.
Proof irrelevance identifies the proofs of the equations used in eqToIso and
upperStarComp. Thus the two original equalities are exactly the restricted laws.
This holds for empty or singleton preorders as well as all degrees and sheaves;
no nonemptiness, directedness, affineness, or existence of a limit is used. -/
theorem etale_limit_reindex_transition_coherence
    {I J : Type u} [Preorder I] [Preorder J]
    (t : J ⥤ I) (D : Iᵒᵖ ⥤ Scheme.{u})
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
    :
    let D' := t.op ⋙ D
    let F' (i : J) := F (t.obj i)
    let φ' {i j : J} (f : i ⟶ j) := φ (t.map f)
    ((∀ i : J, φ' (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D'.map_id (op i)))).hom.app
        (F' i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D'.obj (op i))).hom.app (F' i)) ∧
    (∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      φ' (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D'.map g.op) (D'.map f.op)
          (D'.map (f ≫ g).op) (D'.map_comp g.op f.op)).hom.app (F' i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D'.map g.op)).map (φ' f) ≫ φ' g))  := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    exact @reindex_transition_coherence_aux
      (@upperStar AddCommGrpCat.{u + 1} _ _ _)
      (fun X G ↦ (upperStarId AddCommGrpCat.{u + 1} X).hom.app G)
      (fun {_R _S _T} f g fg h G ↦
        (upperStarComp AddCommGrpCat.{u + 1} f g fg h).hom.app G)
      I J _ _ t D F @φ hidentity hcomposition

end AlgebraicGeometry.Etale
