/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite

/-! # Transport of factorization data by a further base change

Source: Stacks, Limits 01YZ; Categories, fibre products and their canonical comparisons.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem pullback_triangle_coherence
    {C : Type*} [Category* C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {T X Y Z : C} (h : T ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (hf : T ⟶ Y) (hhf : hf = h ≫ f)
    (hfg' : T ⟶ Z) (hhfg : hfg' = hf ≫ g)
    (hhfg' : hfg' = h ≫ fg) (A : P.Over ⊤ Z) :
    (MorphismProperty.Over.pullback P ⊤ h).map
        ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) f g fg hfg).app A).inv ≫
      ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h fg hfg' hhfg').app A).inv =
    ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h f hf hhf).app
        ((MorphismProperty.Over.pullback P ⊤ g).obj A)).inv ≫
      ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) hf g hfg' hhfg).app A).inv := by
  subst fg
  subst hf
  subst hfg'
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Existing models and their two arrow equations transport to any later stage.
This assertion constructs no descended model and asserts no covering.

Source: Stacks, Limits 01YZ and the universal property of fibre products.
(blueprint: lem-weil-pbc-etale-factorization-data-base-change).

Proof: Put P equal to base change along D(t.left). Take the source models to
 be P(Vj). The comparison P(Fj(Z)) ≅ Fk(Z) is the inverse of the canonical
 pullback-composition isomorphism, using D.map_comp and t.w. Postcompose
 P(aj) and P(bj) with these comparisons to define ak and bk. The comparison
 Bk(P(Vj)) ≅ Bj(Vj), followed by d, defines dk. Naturality of pullback
 composition and its associativity give the two displayed limit equations:
 both composites into the triple fibre product have the same projections,
 so the universal property identifies them. The formula for ak is its
 definition. This works for empty families, arbitrary non-affine U_q, and
 identity stage arrows; no geometric descent or covering argument is used. -/
theorem etale_factorizationData_baseChange
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (W : (D.obj (op i₀)).FullAffineEtale)
    (n : ℕ) (V : Fin n → c.pt.Etale)
    (a : ∀ q, V q ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj)
    (U : Fin n → (D.obj (op i₀)).Etale)
    (b : ∀ q, V q ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (U q)) :
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let F := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
    let e := fun (j : Over (op i₀)) (Z : (D.obj (op i₀)).Etale) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app Z
    ∀ (j k : Over (op i₀)) (t : k ⟶ j)
      (Vj : Fin n → (D.obj j.left).Etale)
      (aj : ∀ q, Vj q ⟶ (F j).obj W.obj)
      (bj : ∀ q, Vj q ⟶ (F j).obj (U q))
      (d : ∀ q, (B j).obj (Vj q) ≅ V q),
      (∀ q, (B j).map (aj q) ≫ (e j W.obj).inv = (d q).hom ≫ a q) →
      (∀ q, (B j).map (bj q) ≫ (e j (U q)).inv = (d q).hom ≫ b q) →
      let P := MorphismProperty.Over.pullback @Etale ⊤ (D.map t.left)
      ∃ (ak : ∀ q, P.obj (Vj q) ⟶ (F k).obj W.obj)
        (bk : ∀ q, P.obj (Vj q) ⟶ (F k).obj (U q))
        (dk : ∀ q, (B k).obj (P.obj (Vj q)) ≅ V q)
        (tw : P.obj ((F j).obj W.obj) ≅ (F k).obj W.obj),
        (∀ q, (B k).map (ak q) ≫ (e k W.obj).inv = (dk q).hom ≫ a q) ∧
        (∀ q, (B k).map (bk q) ≫ (e k (U q)).inv = (dk q).hom ≫ b q) ∧
        (∀ q, P.map (aj q) ≫ tw.hom = ak q) := by
  classical
  dsimp only
  intro j k t Vj aj bj d haj hbj
  let Bj := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
  let Bk := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k.left)
  let Fj := MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
  let Fk := MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)
  let P := MorphismProperty.Over.pullback @Etale ⊤ (D.map t.left)
  let r : Fk ≅ Fj ⋙ P := MorphismProperty.Over.pullbackComp
    (D.map t.left) (D.map j.hom) (D.map k.hom) (by rw [← D.map_comp, t.w])
  let s : Bj ≅ P ⋙ Bk := MorphismProperty.Over.pullbackComp
    (c.π.app k.left) (D.map t.left) (c.π.app j.left) (c.w t.left).symm
  let e := fun (j : Over (op i₀)) (Z : (D.obj (op i₀)).Etale) ↦
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app Z
  have coherence (Z : (D.obj (op i₀)).Etale) :
      Bk.map (r.app Z).inv ≫ (e k Z).inv =
        (s.app (Fj.obj Z)).inv ≫ (e j Z).inv := by
    exact pullback_triangle_coherence (@Etale) (c.π.app k.left) (D.map t.left)
      (D.map j.hom) (D.map k.hom) (by rw [← D.map_comp, t.w])
      (c.π.app j.left) (c.w t.left).symm
      (c.π.app (op i₀)) (c.w j.hom).symm (c.w k.hom).symm Z
  let ak := fun q ↦ P.map (aj q) ≫ (r.app W.obj).inv
  let bk := fun q ↦ P.map (bj q) ≫ (r.app (U q)).inv
  let dk := fun q ↦ (s.app (Vj q)).symm ≪≫ d q
  refine ⟨ak, bk, dk, (r.app W.obj).symm, ?_, ?_, fun _ ↦ rfl⟩
  · intro q
    change Bk.map (P.map (aj q) ≫ (r.app W.obj).inv) ≫ (e k W.obj).inv =
      (s.app (Vj q)).inv ≫ (d q).hom ≫ a q
    rw [Functor.map_comp, Category.assoc, coherence]
    have hn : Bk.map (P.map (aj q)) ≫ (s.app (Fj.obj W.obj)).inv =
        (s.app (Vj q)).inv ≫ Bj.map (aj q) := s.inv.naturality (aj q)
    rw [← Category.assoc, hn, Category.assoc, haj q]
  · intro q
    change Bk.map (P.map (bj q) ≫ (r.app (U q)).inv) ≫ (e k (U q)).inv =
      (s.app (Vj q)).inv ≫ (d q).hom ≫ b q
    rw [Functor.map_comp, Category.assoc, coherence]
    have hn : Bk.map (P.map (bj q)) ≫ (s.app (Fj.obj (U q))).inv =
        (s.app (Vj q)).inv ≫ Bj.map (bj q) := s.inv.naturality (bj q)
    rw [← Category.assoc, hn, Category.assoc, hbj q]

end AlgebraicGeometry
