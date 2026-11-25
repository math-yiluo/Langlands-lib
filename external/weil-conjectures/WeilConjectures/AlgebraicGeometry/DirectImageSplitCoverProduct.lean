/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.SplitCoverSectionsLimit

/-!
# Direct image for a split finite cover

Source: literature/stacks-project/etale-cohomology.tex, proof of Lemma 095B
(blueprint: lem-weil-pbc-direct-image-split-cover-product).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- If a scheme is a finite disjoint coproduct of open-and-closed pieces each
isomorphic to the base, its étale direct image is the product of the restrictions.
Source: Stacks Project, Lemma 095B, lines 9982--9991
(blueprint: lem-weil-pbc-direct-image-split-cover-product).

Proof (the five steps of the node):
1. For each étale `W → X`, base change decomposes `W ×_X Y` into the clopen
   pieces over `V j`. The inverse of `V j → X` identifies each piece with `W`;
   the maps `σ j = (id, s j ∘ w)` are their inclusions and form an étale cover.
   Use def-pc-fibre-product, lem-weil-pbc-open-fibre-product, and
   definition-torsion-sheaves--3.
2. Apply the sheaf equalizer condition to this cover. Distinct pieces have empty
   overlap and the empty covering gives `H(∅) = 0`; the two projections on a
   self-overlap agree. Every family of sections is compatible, so the restriction
   map to the product is bijective and additive, including the empty product.
3. The restrictions are sheaves by lem-weil-pbc-etale-inverse-image-restriction.
   Their sectionwise product is a sheaf by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise. The identity
   `h_Y ∘ σ_{j,W'} = σ_{j,W} ∘ h` gives naturality of the restriction maps.
4. Both coefficient maps `Λ_X → Λ_Y|_{s j}` send a constant `λ` to the same
   section, hence agree by def-weil-pbc-sheafification. Semilinearity of the
   restrictions then gives `Λ_X`-linearity (situation-conventions;
   Stacks sites-modules, 03D6 and 03DH).
5. The componentwise inverse is linear and natural, giving the asserted
   isomorphism with the specified components. The sectionwise product has the
   module-sheaf product universal property; for empty `J` it is the zero sheaf.

`localizationRestriction` is the source's literal restriction along composition,
so the equality below specifies the maps of the node, not merely an arbitrary
isomorphism between the two objects. -/
theorem directImage_splitCover_product
    {X Y : Scheme.{u}} {J : Type w} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (f : Y ⟶ X) (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y)
    (t : ∀ j, X ⟶ V j)
    (hcolim : IsColimit (Cofan.mk Y i))
    (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
    (hinv₂ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
    (hopens : ∀ j, AlgebraicGeometry.IsOpenImmersion (i j))
    (hclosed : ∀ j, AlgebraicGeometry.IsClosedImmersion (i j))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    letI : ∀ j, IsOpenImmersion (i j) := hopens
    letI : ∀ j, IsIso (t j) := fun j ↦
      ⟨⟨i j ≫ f, hinv₁ j, hinv₂ j⟩⟩
    let s := fun j ↦ t j ≫ i j
    let R := fun j ↦
      (Etale.localizationRestriction (ModuleCat.{u + 1} Λ) (s j) inferInstance).obj H
    ∃ e : (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj H ≅ ∏ᶜ R,
      ∀ (j : J) (W : X.Etale),
        ((e.hom ≫ Pi.π R j).hom.app (op W)) =
          H.obj.map (MorphismProperty.Over.homMk
            (A := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (s j))).obj W)
            (B := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
            (pullback.lift (𝟙 W.left) (W.hom ≫ s j)
              (by
                change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s j) ≫ f
                simp [s, Category.assoc, hinv₁ j]))
            (by simp)).op := by
  let : ∀ j, IsOpenImmersion (i j) := hopens
  let : ∀ j, IsIso (t j) := fun j ↦ ⟨⟨i j ≫ f, hinv₁ j, hinv₂ j⟩⟩
  let s := fun j ↦ t j ≫ i j
  let R := fun j ↦
    (Etale.localizationRestriction (ModuleCat.{u + 1} Λ) (s j) inferInstance).obj H
  let σ := fun (j : J) (W : X.Etale) ↦ MorphismProperty.Over.homMk
    (A := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (s j))).obj W)
    (B := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
    (pullback.lift (𝟙 W.left) (W.hom ≫ s j)
      (by
        change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s j) ≫ f
        simp [s, Category.assoc, hinv₁ j]))
    (by simp)
  let q : ∀ j, (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj H ⟶ R j := fun j ↦
    ⟨{ app := fun W ↦ H.obj.map (σ j W.unop).op
       naturality := by
         intro W W' h
         change H.obj.map _ ≫ H.obj.map _ = H.obj.map _ ≫ H.obj.map _
         rw [← H.obj.map_comp, ← H.obj.map_comp]
         congr 1
         apply Quiver.Hom.unop_inj
         apply MorphismProperty.Over.Hom.ext
         dsimp [σ]
         apply pullback.hom_ext
         · simp only [Functor.id_obj, Functor.const_obj_obj,
             MorphismProperty.Over.homMk_hom, Over.homMk_left,
             MorphismProperty.Over.pullback_map_left, Category.assoc, limit.lift_π,
             PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left,
             MorphismProperty.Over.map_map_left]
           change 𝟙 _ ≫ h.unop.left = h.unop.left ≫ 𝟙 _
           simp
         · simp [Category.assoc] }⟩
  let c := Fan.mk ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj H) q
  have hc : IsLimit c := by
    apply isLimitOfReflects (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    apply (Fan.isLimitMapConeEquiv
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) _ c).2
    apply evaluationJointlyReflectsLimits
    intro W
    apply (Fan.isLimitMapConeEquiv
      ((evaluation X.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj W) _ _).2
    exact (splitCoverSectionsLimit f V i t hcolim hinv₁ hinv₂ hopens hclosed H W.unop).some
  have : IsIso (Pi.lift q) :=
    (Fan.nonempty_isLimit_iff_isIso_piLift c).mp ⟨hc⟩
  refine ⟨asIso (Pi.lift q), ?_⟩
  intro j W
  change ((Pi.lift q ≫ Pi.π R j).hom.app (op W)) = _
  rw [Pi.lift_comp_π]

end AlgebraicGeometry
