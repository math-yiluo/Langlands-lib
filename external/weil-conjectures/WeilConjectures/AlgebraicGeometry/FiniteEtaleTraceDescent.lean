/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalSums
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent

/-!
# Local sum characterization of finite étale traces

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- For a fixed finite étale morphism, descent of the local sums gives a natural
transformation from pushforward of inverse image to the identity, with the local sum
characterization on every object of the small étale site.
Source: Stacks Project, Section 03SH, after Definition 03SE; SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-descent)

Proof. Write `P_F(W) = F(W ×_X Y)`. The restriction isomorphism identifies this
sheaf with `f_* f⁻¹ F`, naturally in `F`. For a finite clopen splitting of `W ×_X Y`
into copies of `W`, form the sum of restrictions along its sections. Pulling a
splitting back along `W' → W` pulls its sections back, and the pullback universal
property shows that restriction commutes with this sum.

Two splittings give the same sum. Intersect their clopen pieces and project the
intersections to `W`; for each fixed index these images partition `W`. At each point
of `W` this gives a bijection between the two finite sets of pieces. For each such
bijection intersect the corresponding images to obtain an open of `W`. These opens
cover `W`, and on each the sections are equal after reindexing: both invert the same
isomorphism on the intersection. The sums are equal on this cover and hence equal by
sheaf separatedness. If the index sets have different sizes, the base is empty and
its group of sections is zero, so the assertion still holds.

Finite étale local splitting (Stacks 04HN) and covering base change give each `W`
a covering by objects with split pullback of `Y`. For `t ∈ P_F(W)` take its local sums
on this cover. Restriction compatibility and independence of splitting imply that
these sums agree on all overlaps, so glue them to a unique section of `F(W)`. To
compare with a sum on any split object `T → W`, pull the chosen covering back to `T`;
on its members independence of splitting gives the desired equality, and separatedness
gives equality on `T`. Thus the glued section has the universal local sum property.

This property and separatedness prove that gluing is additive, commutes with every
restriction, and commutes with every morphism `F → G`: all of these equalities hold
for the finite local sums on a splitting cover. The additive maps therefore form a
sheaf morphism `P_F → F`, natural in `F`. Compose with the restriction isomorphism
`f_* f⁻¹ F ≅ P_F` to obtain the asserted natural transformation. -/
theorem finiteEtaleTrace_descent {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hfin : IsFinite f) (hf : Etale f) :
    ∃ τ : upperStar AddCommGrpCat.{u + 1} f ⋙ lowerStar AddCommGrpCat.{u + 1} f ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      ∀ F, FiniteEtaleTraceLocalSums f hf F (τ.app F) := by
  classical
  let A := AddCommGrpCat.{u + 1}
  let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
  let P := localizationRestriction A f hf ⋙ lowerStar A f
  have he := finiteEtaleTrace_section_descent f hfin hf
  dsimp only at he
  choose U hU huniq using he
  have hzero (F : Sheaf X.smallEtaleTopology A) (W : X.Etale) : U F W 0 = 0 := by
    apply Eq.symm
    apply huniq F W 0 0
    intro T h J hJ V i t hc hinv₁ hinv₂ hopen hclosed
    simp only [map_zero, Finset.sum_const_zero]
  have hadd (F : Sheaf X.smallEtaleTopology A) (W : X.Etale)
      (s s' : F.obj.obj (op (B.obj W))) : U F W (s + s') = U F W s + U F W s' := by
    apply Eq.symm
    apply huniq F W (s + s') (U F W s + U F W s')
    intro T h J hJ V i t hc hinv₁ hinv₂ hopen hclosed
    simp only [map_add, hU F W s T h J V i t hc hinv₁ hinv₂ hopen hclosed,
      hU F W s' T h J V i t hc hinv₁ hinv₂ hopen hclosed, Finset.sum_add_distrib]
  have hmap (F : Sheaf X.smallEtaleTopology A) {W W' : X.Etale} (k : W' ⟶ W)
      (s : F.obj.obj (op (B.obj W))) :
      F.obj.map k.op (U F W s) = U F W' (F.obj.map (B.map k).op s) := by
    apply huniq F W' (F.obj.map (B.map k).op s) (F.obj.map k.op (U F W s))
    intro T h J hJ V i t hc hinv₁ hinv₂ hopen hclosed
    have hs := hU F W s T (h ≫ k) J V i t hc hinv₁ hinv₂ hopen hclosed
    simpa only [Functor.map_comp, op_comp, ConcreteCategory.comp_apply] using hs
  have hnat {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) (W : X.Etale)
      (s : F.obj.obj (op (B.obj W))) :
      φ.hom.app (op W) (U F W s) = U G W (φ.hom.app (op (B.obj W)) s) := by
    have hn {S T : X.Etale} (h : S ⟶ T) (x : F.obj.obj (op T)) :
        G.obj.map h.op (φ.hom.app (op T) x) =
          φ.hom.app (op S) (F.obj.map h.op x) := by
      exact congrArg (fun k ↦ k x) (φ.hom.naturality h.op).symm
    apply huniq G W (φ.hom.app (op (B.obj W)) s) (φ.hom.app (op W) (U F W s))
    intro T h J hJ V i t hc hinv₁ hinv₂ hopen hclosed
    rw [hn h, hU F W s T h J V i t hc hinv₁ hinv₂ hopen hclosed]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hn (B.map h), hn]
  let β : P ⟶ 𝟭 (Sheaf X.smallEtaleTopology A) :=
    { app := fun F ↦ ObjectProperty.homMk
        { app := fun W ↦ AddCommGrpCat.ofHom
            { toFun := U F W.unop
              map_zero' := hzero F W.unop
              map_add' := hadd F W.unop }
          naturality := by
            intro W W' k
            apply ConcreteCategory.hom_ext
            intro s
            exact (hmap F k.unop s).symm }
      naturality := by
        intro F G φ
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext W
        apply ConcreteCategory.hom_ext
        intro s
        exact (hnat φ W.unop s).symm }
  let c := Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A f hf) (lowerStar A f)
  refine ⟨c.hom ≫ β, ?_⟩
  intro F W J hJ V i t hc hinv₁ hinv₂ hopen hclosed
  apply ConcreteCategory.hom_ext
  intro s
  have hs := hU F W s W (𝟙 W) J V i t hc hinv₁ hinv₂ hopen hclosed
  have hid :
      (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
        (((lowerStar A f).map
          (((upperStarIsoLocalizationRestriction A f hf).app F).hom)).hom.app (op W)) =
        𝟙 (F.obj.obj (op (B.obj W))) := by
    change _ ≫ (((upperStarIsoLocalizationRestriction A f hf).app F).hom.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) = _
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom]
    simp only [Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    rfl
  change U F W
    ((((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ≫
        (((lowerStar A f).map
          (((upperStarIsoLocalizationRestriction A f hf).app F).hom)).hom.app (op W))) s) = _
  rw [hid]
  rw [op_id, F.obj.map_id] at hs
  change U F W s = _
  have hb : (MorphismProperty.Over.pullback @Etale ⊤ f ⋙
      MorphismProperty.Over.map ⊤ hf).map (𝟙 W) = 𝟙 (B.obj W) := B.map_id W
  rw [hb, op_id, F.obj.map_id] at hs
  have heval {M N : AddCommGrpCat.{u + 1}} (v : J → (M ⟶ N)) (x : M) :
      (∑ j, v j) x = ∑ j, v j x := by
    change ((∑ j, v j).hom) x = _
    have hv := map_sum (AddCommGrpCat.homAddEquiv (M := M) (N := N)) v Finset.univ
    change (∑ j, v j).hom = ∑ j, (v j).hom at hv
    rw [hv]
    exact AddMonoidHom.finsetSum_apply _ _ _
  rw [heval]
  exact hs

end AlgebraicGeometry.Etale
