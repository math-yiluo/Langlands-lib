/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsExistence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsUniqueness

/-!
# Existence and uniqueness of the finite étale trace

Source: Stacks Project, Section 03SH, following Definition 03SE
(blueprint: lem-weil-pbc-finite-etale-trace-exists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The unique family of finite étale trace morphisms, natural in the abelian sheaf,
compatible with étale localization, and equal to the sum of restrictions for every finite
clopen splitting (including the empty splitting). A splitting is written as the split covers of
lem-weil-pbc-direct-image-split-cover-product: pieces `i j : V j ⟶ Y` exhibiting `Y` as their
coproduct (`IsColimit (Cofan.mk Y i)`, open and closed immersions, hence pairwise disjoint and
covering), `t j` the inverse of `i j ≫ f`, `s j = t j ≫ i j`, and
`σ j = (id_W, s j ∘ w) = pullback.lift (𝟙 W.left) (W.hom ≫ s j)`. Source: Stacks, Section 03SH after
Definition 03SE (blueprint: lem-weil-pbc-finite-etale-trace-exists).

Proof plan, following the node's ten steps:
1. Identify `f_* f⁻¹ F` with the sheaf `W ↦ F(W ×_X Y)` using the natural restriction
isomorphism (lem-weil-pbc-etale-inverse-image-restriction). Giving a trace is equivalent to
giving an additive presheaf map from this sheaf to `F`.
2. For a finite clopen splitting define the local sum of restrictions along its sections.
It is additive and natural in `F` (situation-conventions).
3. Pull a splitting back along an étale-site morphism. Cartesian-square pasting and open
fibre products identify its pieces and sections; local sums commute with restriction
(lem-weil-pbc-cartesian-square-pasting, lem-weil-pbc-open-fibre-product).
4. Two splittings give the same sum: intersect their pieces and cover the base by the opens
on which their sections agree up to a permutation. Reindex the finite sums and use sheaf
separatedness. Unequal cardinalities force the base empty, whose sections are zero.
5. Finite étale morphisms split étale locally (lem-weil-pbc-finite-etale-etale-local-split,
Stacks 04HN). Pull the resulting covering back to every site object using
lem-weil-pbc-etale-covering-base-change.
6. Descend the local sums: they agree on overlaps by steps 3 and 4, so the sheaf condition
gives a unique section. Its restrictions agree with the sum for every pulled-back splitting.
7. Uniqueness in this descent proves additivity, compatibility with restriction, and
naturality in `F`. Transport the resulting presheaf morphism back by the restriction iso.
8. In the split case the identity covering computes the descended section as the sum;
the coproduct case follows from definition-torsion-sheaves--3.
9. Cartesian pasting identifies the two iterated fibre products. Transporting splittings
along this identification shows localization compatibility for `F|_X'`; naturality in the
restriction iso gives the assertion for `g⁻¹ F`.
10. Any competing family has the same local sums by localization and the split formula.
Sheaf separatedness on the splitting covering makes its components equal to the constructed
ones, so the family is unique. -/
theorem existsUnique_finiteEtaleTrace :
    let A := AddCommGrpCat.{u + 1}
    let B := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f) (W : X.Etale) ↦
      (MorphismProperty.Over.map ⊤ hf).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
    let T := ∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsFinite f) (_ : Etale f)
      (F : Sheaf X.smallEtaleTopology A),
      (lowerStar A f).obj ((upperStar A f).obj F) ⟶ F
    ∃! tr : T,
      let bar := fun {X Y : Scheme.{u}} (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (W : X.Etale) ↦
        (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
            (tr X Y f hfin hf F).hom.app (op W)
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F G : Sheaf X.smallEtaleTopology A) (φ : F ⟶ G),
        tr X Y f hfin hf F ≫ φ =
          (lowerStar A f).map ((upperStar A f).map φ) ≫ tr X Y f hfin hf G) ∧
      (∀ (X Y X' : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (g : X' ⟶ X) (hg : Etale g) (F : Sheaf X.smallEtaleTopology A),
        letI := hfin
        letI := hf
        let f' := pullback.snd f g
        let hf' : Etale f' := inferInstance
        let F' := (upperStar A g).obj F
        ∀ (W : X'.Etale)
          (κ : (MorphismProperty.Over.map ⊤ hg).obj (B f' hf' W) ≅
            B f hf ((MorphismProperty.Over.map ⊤ hg).obj W)),
          κ.hom.left ≫ pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' →
          κ.hom.left ≫ pullback.snd (W.hom ≫ g) f =
            pullback.snd W.hom f' ≫ pullback.fst f g →
          bar f' inferInstance hf' F' W ≫
              ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app (op W) =
            ((upperStarIsoLocalizationRestriction A g hg).app F).hom.hom.app
                (op (B f' hf' W)) ≫ F.obj.map κ.inv.op ≫
              bar f hfin hf F ((MorphismProperty.Over.map ⊤ hg).obj W)) ∧
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (hfin : IsFinite f) (hf : Etale f)
          (F : Sheaf X.smallEtaleTopology A) (J : Type u) [Fintype J]
          (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y) (t : ∀ j, X ⟶ V j)
          (_ : IsColimit (Cofan.mk Y i))
          (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
          (_ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
          (_ : ∀ j, IsOpenImmersion (i j))
          (_ : ∀ j, IsClosedImmersion (i j))
          (W : X.Etale),
          bar f hfin hf F W = ∑ j, F.obj.map (MorphismProperty.Over.homMk
            (A := W) (B := B f hf W)
            (pullback.lift (𝟙 W.left) (W.hom ≫ t j ≫ i j)
              (by simp [Category.assoc, hinv₁]))
            (by simp [B, Category.assoc, hinv₁])).op) := by
  have he := finiteEtaleTrace_exists
  have hu := finiteEtaleTrace_unique
  rcases he with ⟨tr, htr⟩
  exact ⟨tr, htr, fun tr' h' => (hu tr tr' htr h').symm⟩

end AlgebraicGeometry.Etale
