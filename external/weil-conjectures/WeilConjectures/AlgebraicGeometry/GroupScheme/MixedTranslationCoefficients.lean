/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.InvariantCoefficients
import WeilConjectures.AlgebraicGeometry.GroupScheme.TwoParameterTranslationAction

/-!
# The mixed coefficient of a commutator of right translations

Source: the second coefficient step of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint
`def-wf-lie-algebra-derivation`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

private theorem mul_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.dualNumbers.dualNumbers ≫ Y.dualNumbersMul = X.dualNumbersMul ≫ f.dualNumbers := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.mapRingHom (DualNumber.mapRingHom (f.app U).hom)
      (DualNumber.mulRingHom a) =
    DualNumber.mulRingHom (DualNumber.mapRingHom (f.app U).hom a)
  exact RingHom.congr_fun (DualNumber.mapRingHom_mapRingHom_comp_mulRingHom (f.app U).hom) a

set_option backward.isDefEq.respectTransparency false in
private theorem mixed_appLE {X : Scheme.{u}} (m : X.dualNumbers ⟶ X)
    (hm : m.base = 𝟙 _) (U : X.Opens)
    (e : U ≤ (X.dualNumbersMul ≫ m) ⁻¹ᵁ U) (e' : U ≤ m ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    ((X.dualNumbersMul ≫ m).appLE U U e a).snd.snd = (m.appLE U U e' a).snd := by
  rcases m with ⟨⟨⟨vb, vc⟩, vp⟩⟩
  change vb = 𝟙 _ at hm
  subst vb
  simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, homOfLE_refl, op_id]
  erw [X.dualNumbers.dualNumbers.presheaf.map_id, Category.comp_id,
    X.dualNumbers.presheaf.map_id, Category.comp_id]
  simp only [Scheme.dualNumbersMul, Scheme.Hom.app, TopCat.Presheaf.comp_app,
    Functor.whiskerLeft_app, TopCat.Presheaf.Pushforward.id_inv_app, Category.comp_id]
  change (DualNumber.mulRingHom (vc.app (Opposite.op U) a)).snd.snd = _
  simp only [DualNumber.snd_mulRingHom, TrivSqZeroExt.snd_inr]
  rfl

private theorem mixed_operator_coefficient {R : Type u} [CommRing R]
    (D E : AddMonoid.End R) (a : R) :
    (epsilonSectionAction D (deltaSectionAction E
      (epsilonSectionAction (-D)
        (deltaSectionAction (-E) (TrivSqZeroExt.inl (TrivSqZeroExt.inl a)))))).snd.snd =
      D (E a) - E (D a) := by
  have hn (F : AddMonoid.End R) (b : R) : (-F) b = -F b := rfl
  simp [epsilonSectionAction, deltaSectionAction, hn, sub_eq_add_neg]

private theorem twoParameterRightTranslation_mixed (t : infPoints G) :
    twoParameterRightTranslation G (Scheme.dualNumbersMulOver S ≫ t.1) =
      G.left.dualNumbersMul ≫ infinitesimalRightTranslation G t := by
  let X := Over.mk
    (G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom)
  let Y := Over.mk (G.left.dualNumbersProj ≫ G.hom)
  let f : X ⟶ Y := Over.homMk G.left.dualNumbersMul (by
    change G.left.dualNumbersMul ≫ G.left.dualNumbersProj ≫ G.hom =
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj ≫ G.hom
    rw [Scheme.dualNumbersMul_comp_proj_assoc])
  let p : Y ⟶ G := Over.homMk G.left.dualNumbersProj rfl
  let q : Y ⟶ G := Over.homMk (G.hom.dualNumbers ≫ t.1.left) (by
    rw [Category.assoc, Over.w t.1]
    exact Scheme.Hom.dualNumbers_comp_proj G.hom)
  have hp : (f ≫ p).left =
      G.left.dualNumbers.dualNumbersProj ≫ G.left.dualNumbersProj := by
    exact Scheme.dualNumbersMul_comp_proj _
  have hq : (f ≫ q).left =
      G.hom.dualNumbers.dualNumbers ≫ (Scheme.dualNumbersMulOver S ≫ t.1).left := by
    change G.left.dualNumbersMul ≫ G.hom.dualNumbers ≫ t.1.left =
      G.hom.dualNumbers.dualNumbers ≫ S.dualNumbersMul ≫ t.1.left
    rw [← Category.assoc, ← mul_naturality, Category.assoc]
  have h := congrArg Over.Hom.left (MonObj.comp_mul f p q)
  change G.left.dualNumbersMul ≫ infinitesimalRightTranslation G t = _ at h
  rw [h]
  unfold twoParameterRightTranslation
  dsimp only
  apply congrArg Over.Hom.left
  congr 1
  · exact Over.OverMorphism.ext hp.symm
  · exact Over.OverMorphism.ext hq.symm

/-- If the two-parameter commutator of v and w is the mixed lift of t, its invariant
coefficient is the commutator of the invariant coefficient operators of v and w.

Source: the second coefficient step of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`.
(blueprint: lem-ag-mixed-translation-coefficients)

Proof: Pull the three explicit right translations back to G[ε][δ]. On sections the
first two act as 1+εD_v and 1+δD_w, with derivations acting coefficientwise and fixing
both parameters. Their inverses act as 1-εD_v and 1-δD_w. Composition of comorphisms
in the order specified by v_ε w_δ v_ε⁻¹ w_δ⁻¹ gives
1+εδ(D_v D_w-D_w D_v), by ε²=δ²=0. The hypothesis identifies this translation with
the translation attached to t pulled back by η↦εδ, whose comorphism is 1+εδD_t.
Equality of the εδ coefficients gives the asserted equality on every open, and hence
of the families of additive endomorphisms. The construction uses right translation of
the universal point, so the coefficient identity is sheafwise without affine,
smoothness, nonemptiness, or characteristic hypotheses. -/
theorem invariantCoefficient_of_mixed_commutator (v w t : infPoints G)
    (h : Scheme.dualNumbersMulOver S ≫ t.1 =
      (Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹) :
    invariantCoefficient G t =
      invariantCoefficient G v * invariantCoefficient G w -
        invariantCoefficient G w * invariantCoefficient G v := by
  have ht := twoParameterRightTranslation_mixed G t
  have heq := congrArg (twoParameterRightTranslation G) h
  have hb : (infinitesimalRightTranslation G t).base = 𝟙 _ := by
    have b := congrArg (fun f : G.left ⟶ G.left ↦ f.base)
      (infinitesimalRightTranslation_reduction G t)
    exact b
  ext U a
  let z := (Scheme.dualNumbersProjεOver S ≫ v.1) *
    (Scheme.dualNumbersProjδOver S ≫ w.1) *
      (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
        (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹
  have hz : twoParameterRightTranslation G z =
      G.left.dualNumbersMul ≫ infinitesimalRightTranslation G t := heq.symm.trans ht
  have e : U ≤ (twoParameterRightTranslation G z) ⁻¹ᵁ U := by
    rw [hz]
    change U ≤ (TopologicalSpace.Opens.map
      (G.left.dualNumbersMul ≫ infinitesimalRightTranslation G t).base).obj U
    rw [Scheme.Hom.comp_base, hb]
    exact le_rfl
  have hc := twoParameterRightTranslation_commutator_app G v w U e a
  have hm : ((twoParameterRightTranslation G z).appLE U U e a).snd.snd =
      invariantCoefficient G t U a := by
    have aux : ∀ (n : G.left.dualNumbers.dualNumbers ⟶ G.left)
        (en : U ≤ n ⁻¹ᵁ U),
        n = G.left.dualNumbersMul ≫ infinitesimalRightTranslation G t →
        (n.appLE U U en a).snd.snd = invariantCoefficient G t U a := by
      intro n en hn
      subst n
      exact mixed_appLE _ hb U en (infinitesimalRightTranslation_preimage G t U) a
    exact aux _ e hz
  change invariantCoefficient G t U a =
    invariantCoefficient G v U (invariantCoefficient G w U a) -
      invariantCoefficient G w U (invariantCoefficient G v U a)
  rw [← hm, congrArg (fun x ↦ x.snd.snd) hc]
  exact mixed_operator_coefficient _ _ a

end AlgebraicGeometry.GrpObj
