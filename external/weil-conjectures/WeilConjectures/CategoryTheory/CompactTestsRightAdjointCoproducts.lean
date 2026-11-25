/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.EssentiallySmall

import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Compact tests for preservation of coproducts by a right adjoint

Source: Stacks Project, Tag 0A9R; the explicit compact-test and indexing-universe
argument in `lem-sc-compact-tests-right-adjoint-coproducts`.
-/

@[expose] public section

universe u v uC uD wC wD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The nonzero summands of an existing coproduct inject into its endomorphisms. -/
private theorem coproduct_small_support
    {D : Type uD} [Category.{wD} D] [Preadditive D] [LocallySmall.{u} D]
    {I : Type v} (K : I → D) (t : Cofan K) (ht : IsColimit t) :
    Small.{u} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

/-- Shrinking nonzero support extends preservation to every indexing universe. -/
private theorem preservesCoproducts_of_small
    {D : Type uD} [Category.{wD} D] [Preadditive D] [LocallySmall.{u} D]
    {C : Type uC} [Category.{wC} C] [Preadditive C]
    (c : D ⥤ C) [c.PreservesZeroMorphisms]
    (hsmall : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) c)
    (I : Type v) : PreservesColimitsOfShape (Discrete I) c := by
  classical
  have hpres (K : I → D) : PreservesColimit (Discrete.functor K) c := by
    refine ⟨fun {t} ht ↦ ⟨?_⟩⟩
    let t₀ : Cofan K := t
    have hsupport : Small.{u} {i // ¬ IsZero (K i)} := coproduct_small_support K t₀ ht
    let J := {i // ¬ IsZero (K i)}
    have : PreservesColimitsOfShape (Discrete (Shrink.{u} J)) c := hsmall _
    have : PreservesColimitsOfShape (Discrete J) c :=
      preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink J)).symm c
    let U : J → D := fun i ↦ K i.val
    let r : Cofan U := Cofan.mk t.pt (fun i ↦ t₀.inj i.val)
    have hr : IsColimit r := by
      refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
        (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
      · intro s i
        obtain ⟨i, hi⟩ := i
        change t.ι.app (Discrete.mk i) ≫ _ = _
        rw [ht.fac]
        simp only [Cofan.mk_ι_app, dite_eq_left hi]
      · intro s m hm
        apply ht.hom_ext
        intro ⟨i⟩
        rw [ht.fac]
        by_cases hi : ¬ IsZero (K i)
        · simpa only [r, cofan_mk_inj, t₀, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
            using hm ⟨i, hi⟩
        · exact (not_not.mp hi).eq_of_src _ _
    let q : Cofan (fun i ↦ c.obj (U i)) :=
      Cofan.mk (c.obj t.pt) (fun i ↦ c.map (t₀.inj i.val))
    have hq : IsColimit q := isColimitCofanMkObjOfIsColimit c U _ hr
    refine { desc := fun s ↦ hq.desc (Cofan.mk s.pt
        (fun i ↦ s.ι.app (Discrete.mk i.val))), fac := ?_, uniq := ?_ }
    · intro s ⟨i⟩
      by_cases hi : ¬ IsZero (K i)
      · exact hq.fac (Cofan.mk s.pt (fun i ↦ s.ι.app (Discrete.mk i.val)))
          (Discrete.mk ⟨i, hi⟩)
      · exact (c.map_isZero (not_not.mp hi)).eq_of_src _ _
    · intro s m hm
      apply Cofan.IsColimit.hom_ext hq
      intro i
      exact (hm (Discrete.mk i.val)).trans
        (hq.fac (Cofan.mk s.pt (fun i ↦ s.ι.app (Discrete.mk i.val)))
          (Discrete.mk i)).symm
  exact preservesColimitsOfShape_of_discrete c

/-- Compactness and adjunction identify the Hom map of the small comparison. -/
private theorem compactTests_small
    {C : Type uC} [Category.{wC} C] [Preadditive C] [HasCoproducts.{u} C]
    {D : Type uD} [Category.{wD} D] [Preadditive D] [HasCoproducts.{u} D]
    (R : C ⥤ D) (c : D ⥤ C) (adj : R ⊣ c) [R.Additive]
    (S : Type u) (G : S → C)
    (hcompact : ∀ s, IsCompactObject (G s) ∧ IsCompactObject (R.obj (G s)))
    (hdetect : ∀ (A B : C) (g : A ⟶ B),
      (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g)
    (I : Type u) : PreservesColimitsOfShape (Discrete I) c := by
  classical
  have hpres (K : I → D) : PreservesColimit (Discrete.functor K) c := by
    have hq : IsIso (sigmaComparison c K) := by
      apply hdetect
      intro s
      let L : ∀ i, (R.obj (G s) ⟶ K i) →+ (G s ⟶ c.obj (K i)) :=
        fun i ↦ (adj.homAddEquiv (G s) (K i)).toAddMonoidHom
      let a := DirectSum.toAddMonoid
        (fun i ↦ Preadditive.rightComp (G s) (Sigma.ι (fun i ↦ c.obj (K i)) i))
      let b := DirectSum.toAddMonoid
        (fun i ↦ Preadditive.rightComp (R.obj (G s)) (Sigma.ι K i))
      let B := (adj.homAddEquiv (G s) (∐ K)).toAddMonoidHom
      let Q := Preadditive.rightComp (G s) (sigmaComparison c K)
      have square : Q.comp (a.comp (DirectSum.map L)) = B.comp b := by
        apply DirectSum.addHom_ext
        intro i f
        simp only [AddMonoidHom.comp_apply, DirectSum.map_of]
        dsimp [a, b]
        rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
        change (adj.homEquiv (G s) (K i) f ≫
          Sigma.ι (fun i ↦ c.obj (K i)) i) ≫ sigmaComparison c K =
          adj.homEquiv (G s) (∐ K) (f ≫ Sigma.ι K i)
        rw [Category.assoc, ι_comp_sigmaComparison, adj.homEquiv_naturality_right]
      have hL : Function.Bijective (DirectSum.map L) :=
        ⟨(DirectSum.map_injective L).2 (fun i ↦ (adj.homEquiv _ _).injective),
          (DirectSum.map_surjective L).2 (fun i ↦ (adj.homEquiv _ _).surjective)⟩
      have ha : Function.Bijective a := (hcompact s).1 I _
      have hb : Function.Bijective b := (hcompact s).2 I K
      have hcomp : Function.Bijective (Q ∘ (a ∘ DirectSum.map L)) := by
        change Function.Bijective (Q.comp (a.comp (DirectSum.map L)))
        rw [square]
        exact (adj.homEquiv _ _).bijective.comp hb
      exact (Function.Bijective.of_comp_iff Q (ha.comp hL)).mp hcomp
    exact PreservesCoproduct.of_iso_comparison c K
  exact preservesColimitsOfShape_of_discrete c

/-- An adjunction whose left adjoint takes a small detecting family of compact objects
 to compact objects has a coproduct-preserving right adjoint.
Source: Stacks Project, Tag 0A9R, adjunction Hom calculation and conclusion.
(blueprint: lem-sc-compact-tests-right-adjoint-coproducts).

Proof. For a u-small family K form the coproduct comparison for c. Compactness of
G s identifies Hom(G s, the coproduct of c(K i)) with the direct sum of Hom(G s,c(K i)).
Adjunction identifies these summands with Hom(R(G s),K i). Compactness of R(G s)
identifies their sum with Hom(R(G s), the coproduct of K i), and adjunction identifies
this with Hom(G s,c(the coproduct of K i)). Naturality of adjunction on each
coprojection says the composite bijection is postcomposition with the comparison.
The detecting hypothesis makes that comparison an isomorphism. Adjoint functors
between preadditive categories are additive since they preserve finite biproducts.

For a family in any larger indexing universe with an existing coproduct B in D,
its nonzero indices form a u-small set. Indeed, each coprojection has a retraction
which is the identity on that summand and zero on the others. The corresponding
nonzero idempotents in End(B) are distinct, so these indices inject into the u-small
set End(B). Shrink that support to Type u. Its coproduct is B: removing zero terms
and reindexing preserve the universal property. Since c is a right adjoint, it
preserves the terminal object, which in a preadditive category with an initial
object is also zero. Thus the same removal and reindexing apply to c(K i).
The u-small case now proves preservation for the original family. This argument
also covers the empty family; compactness identifies its Hom groups with zero. -/
theorem compactTests_rightAdjoint_preservesCoproducts
    {C : Type uC} [Category.{wC} C] [Preadditive C] [HasCoproducts.{u} C]
    {D : Type uD} [Category.{wD} D] [Preadditive D] [HasCoproducts.{u} D]
    [LocallySmall.{u} D]
    (R : C ⥤ D) (c : D ⥤ C) (adj : R ⊣ c)
    (S : Type u) (G : S → C)
    (hcompact : ∀ s, IsCompactObject (G s) ∧ IsCompactObject (R.obj (G s)))
    (hdetect : ∀ (A B : C) (g : A ⟶ B),
      (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g) :
    ∀ I : Type v, PreservesColimitsOfShape (Discrete I) c := by
  have : R.IsLeftAdjoint := adj.isLeftAdjoint
  have : HasFiniteCoproducts C := hasFiniteCoproducts_of_hasCoproducts C
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  have : R.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts R
    exact Functor.additive_of_preservesBinaryBiproducts R
  have hsmall := compactTests_small R c adj S G hcompact hdetect
  have : c.Additive := adj.right_adjoint_additive
  exact preservesCoproducts_of_small c hsmall

end CategoryTheory
