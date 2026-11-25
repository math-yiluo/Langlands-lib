/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineOpenInverseImageRefinementData
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsEventualCompatibility
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Eventual agreement of a finite family of local unit lifts -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- A finite family of affine local sections with agreeing limit images has a
covering refinement at a later open stage on which its restrictions are compatible.
Source: Stacks Project, Tag 03Q6, proof steps (2)--(4), and Tag 09XM
(equality locus of inverse-image sections).
(blueprint: lem-weil-pbc-affine-open-inverse-image-compatible-refinement).

Proof: On each pairwise overlap over D(j), take the difference of the two sections.
Its inverse-image unit is zero: both local unit images restrict from t. The overlap
is affine, since both members and D(j) are affine. The zero-neighbourhood argument
puts the limit image in an open on which the difference is zero. The compact affine
limit criterion supplies a later stage whose overlap lies in this open. Cofilteredness
puts these finitely many stages over j at one common stage, equalizing the finitely
many arrows to j. Pull back the original covering along this stage map to obtain
V', v', gamma. Cover stability gives the stage cover, and its pullback to the limit
still covers the terminal object. The restricted differences are zero on all pairwise
pullbacks. Every pair of arrows with equal composites factors through that pairwise
pullback, giving the stated compatibility. The terminal maps pi' are the composites
of the old pi with the base changes of gamma. If B is empty, the original covering
forces D(j) empty and all compatibility conditions are vacuous; take k=j. The same
proof includes empty limits, singleton systems and the zero sheaf. This theorem
neither constructs a global section nor assumes an amalgamation exists. -/
theorem affineOpenSections_inverse_image_compatible_refinement
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))))
    (j : J) (B : Type (u + 1)) [Finite B]
    (V : B → X.Etale) (v : ∀ b, V b ⟶ D.obj j)
    (s : ∀ b, F.obj.obj (op (V b)))
    (π : ∀ b, p.Etale.obj (V b) ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (hV : ∀ b, IsAffine (V b).left)
    (hv : Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j))
    (hπ : Sieve.ofArrows (fun b ↦ p.Etale.obj (V b)) π ∈
      c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)))
    (hs : ∀ b, (H.obj F).obj.map (π b).op t =
      (hH.unit.app F).hom.app (op (V b)) (s b)) :
    ∃ (k : J) (f : k ⟶ j) (V' : B → X.Etale)
      (v' : ∀ b, V' b ⟶ D.obj k) (γ : ∀ b, V' b ⟶ V b)
      (π' : ∀ b, p.Etale.obj (V' b) ⟶ Scheme.Etale.mk (𝟙 c.pt)),
      (∀ b, v' b ≫ D.map f = γ b ≫ v b) ∧
      Sieve.ofArrows V' v' ∈ X.smallEtaleTopology (D.obj k) ∧
      Sieve.ofArrows (fun b ↦ p.Etale.obj (V' b)) π' ∈
        c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)) ∧
      (∀ b, p.Etale.map (γ b) ≫ π b = π' b) ∧
      ∀ ⦃W : X.Etale⦄ ⦃b b' : B⦄ (a : W ⟶ V' b) (a' : W ⟶ V' b'),
        a ≫ v' b = a' ≫ v' b' →
        F.obj.map a.op (F.obj.map (γ b).op (s b)) =
          F.obj.map a'.op (F.obj.map (γ b').op (s b')) := by
  classical
  have hpair : ∀ z : B × B, ∃ (k : J) (f : k ⟶ j),
      ∀ (U : X.Etale) (a : U ⟶ V z.1) (a' : U ⟶ V z.2) (q : U ⟶ D.obj k),
        a ≫ v z.1 = q ≫ D.map f → a' ≫ v z.2 = q ≫ D.map f →
        F.obj.map a.op (s z.1) = F.obj.map a'.op (s z.2) := by
    intro z
    exact affineOpenSections_pair_eventual_agreement D c p hp hc H hH F t j
      (V z.1) (V z.2) (v z.1) (v z.2) (s z.1) (s z.2)
      (π z.1) (π z.2) (hV z.1) (hV z.2) (hs z.1) (hs z.2)
  choose kp fp heq using hpair
  obtain ⟨k, f, g, hg⟩ := IsCofiltered.wideCospan fp
  obtain ⟨V', v', γ, π', hsq, hcover, hlimit, hπ'⟩ :=
    affineOpenSections_refinement_data D c p hp j k f B V v π hv hπ
  refine ⟨k, f, V', v', γ, π', hsq, hcover, hlimit, hπ', ?_⟩
  intro W b b' a a' haa'
  have hleft : (a ≫ γ b) ≫ v b =
      (a ≫ v' b ≫ D.map (g (b, b'))) ≫ D.map (fp (b, b')) := by
    simp only [Category.assoc, ← hsq b, ← D.map_comp, hg]
  have hright : (a' ≫ γ b') ≫ v b' =
      (a ≫ v' b ≫ D.map (g (b, b'))) ≫ D.map (fp (b, b')) := by
    simp only [Category.assoc, ← hsq b', ← D.map_comp, hg]
    simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ D.map f) haa'.symm
  have h := heq (b, b') W (a ≫ γ b) (a' ≫ γ b')
    (a ≫ v' b ≫ D.map (g (b, b'))) hleft hright
  simpa only [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply] using h

