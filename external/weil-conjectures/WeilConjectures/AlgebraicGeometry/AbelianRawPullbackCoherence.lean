/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackCoherenceBase
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend

/-! # Coherence of varying-coefficient raw pullbacks

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-raw-pullback-coherence).
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Raw pullback obeys coefficient identity, composition and cocone laws.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 03CB for inverse-image composition.
(blueprint: lem-sbc-abelian-raw-pullback-coherence).

Proof: First bundle each raw function as a homomorphism: derived inverse image is
additive, and precomposition/postcomposition with fixed morphisms preserve zero
and addition. For a restriction map of test objects, naturality of upperStarComp
moves the source restriction past the composition comparison. Naturality of the
single-functor comparison moves it past its inverse. Derived pullback preserves
composition, leaving the restriction in the target followed by the same coefficient
and shift factors. Thus the component homomorphisms are natural in the test object;
use them for tau and beta. Their prescribed component equations are reflexivity.
Expand the five factors in abelianHigherDirectImageRawPullback.
For identities, D.map_id identifies the scheme arrow with the identity and hphiid
identifies its coefficient map with upperStarId. The identity coherence of upperStarComp
cancels the source identity comparison with the single-functor comparison. Naturality
and shift compatibility of the derived identity comparison cancel the remaining factors.
For a composite, move the inner factors through the outer derived inverse image using
map_comp. Naturality of the single-functor comparison cancels its adjacent inverse
and direct components. Associativity of upperStarComp identifies the two source
comparisons with the one for the composite. The coefficient comparisons agree by
hphicomp; shift compatibility combines the two shift factors. This gives equality on
classes at every test object. Extensionality of group homomorphisms and natural
transformations gives the stated identity and composition equations. Finally substitute
hH into the coefficient map for a limit leg. Naturality of colimit.ι H identifies
H.map f followed by colimit.ι H j with colimit.ι H i. Cancelling eH j and its inverse
and applying the same composite calculation proves the cocone law. These arguments
use no limit, qcqs, affineness or continuity assumption; they hold for zero sheaves
and empty test objects as well as in degree zero. -/
theorem abelianRawPullback_coherent {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ) :
    ∃ (τ : ∀ {i j : I} (_f : i ⟶ j),
        abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
          abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j))
      (β : ∀ i : I, abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
        abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)),
      (∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (τ f).app (op V) t = abelianHigherDirectImageRawPullback (D.map f.op).left
          (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
          (F i) (F j) (φ f) V t) ∧
      (∀ (i : I) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (β i).app (op V) t = abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t) ∧
      (∀ i : I, τ (𝟙 i) = 𝟙 _) ∧
      (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), τ (f ≫ g) = τ f ≫ τ g) ∧
      (∀ {i j : I} (f : i ⟶ j), τ f ≫ β j = β i) := by
  rcases abelianRawPullback_coherent_base D c F φ hφid hφcomp H eH hH p with
    ⟨τ, β, hτ, hβ, hid, hcomp⟩
  refine ⟨τ, β, hτ, hβ, hid, hcomp, ?_⟩
  exact abelianRawPullback_coherent_extend D c F φ hφid hφcomp H eH hH p
    τ β hτ hβ

end AlgebraicGeometry.Etale
