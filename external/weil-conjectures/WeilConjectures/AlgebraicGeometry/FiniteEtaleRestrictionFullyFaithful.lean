/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

import WeilConjectures.AlgebraicGeometry.HenselianClopenRestriction
import WeilConjectures.AlgebraicGeometry.FiniteEtaleGraphClopen
import WeilConjectures.AlgebraicGeometry.FiniteEtaleGraphBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClopenRestrictionRank

/-! # Full faithfulness of finite étale restriction
Source: corrected blueprint theorem-finite-etale-covers-proper-henselian--2, proof steps 1–6;
Stacks Project, Tags 0GS2 (the result) and 0A0B (clopen restriction).
(blueprint: lem-weil-pbc-finite-etale-restriction-fully-faithful)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem rank_one_of_clopen_injective
    {X X₀ S S₀ : Scheme.{u}} (q : X ⟶ S) [IsFinite q] [Etale q]
    (j : X₀ ⟶ X) (q₀ : X₀ ⟶ S₀) (i : S₀ ⟶ S) (h : IsPullback j q₀ q i)
    (hinj : ∀ U V : Set S, IsOpen U ∧ IsClosed U → IsOpen V ∧ IsClosed V →
      i.base ⁻¹' U = i.base ⁻¹' V → U = V)
    (W : X.Opens) (hW : IsClosed (W : Set X)) :
    IsIso (W.ι ≫ q) ↔ IsIso ((j ⁻¹ᵁ W).ι ≫ q₀) := by
  obtain ⟨hfin, het, hfin₀, het₀, hrank⟩ :=
    Scheme.finrank_restrict_isClopen_of_isPullback q j q₀ i h W hW
  have := hfin
  have := het
  have := hfin₀
  have := het₀
  rw [Scheme.Hom.isIso_iff_finrank_eq, Scheme.Hom.isIso_iff_finrank_eq]
  constructor
  · intro hr
    funext x
    rw [hrank, hr]
    rfl
  · intro hr
    have hopen := (W.ι ≫ q).isLocallyConstant_finrank.isOpen_fiber 1
    have hclosed := (W.ι ≫ q).isLocallyConstant_finrank.isClosed_fiber 1
    have heq : {x : S | (W.ι ≫ q).finrank x = 1} = Set.univ := by
      apply hinj _ _ ⟨hopen, hclosed⟩ ⟨isOpen_univ, isClosed_univ⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [← hrank, hr]
      rfl
    funext x
    exact Set.eq_univ_iff_forall.mp heq x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Finite étale restriction is fully faithful over a proper henselian pair.
Source: corrected blueprint theorem-finite-etale-covers-proper-henselian--2, proof steps 1–6;
Stacks Project, Tags 0GS2 (the result) and 0A0B (clopen restriction).
(blueprint: lem-weil-pbc-finite-etale-restriction-fully-faithful)

Proof: For finite étale U,V over Y, morphisms U → V over Y correspond to sections of
P = V ×[Y] U → U. A section of this finite étale separated morphism is an open and
closed immersion; conversely a clopen W in P whose projection to U is an isomorphism
recovers a unique section. These correspondences commute with base change. The schemes
U and P are proper over A. Clopen restriction for proper henselian schemes lifts a
clopen W₀ in P₀ uniquely to W in P. Its projection is finite étale. Its rank-one locus
is clopen in U and contains U₀ because W₀ → U₀ is an isomorphism; the complementary
clopen misses U₀, hence is empty by injectivity of clopen restriction. The projection
therefore has rank one everywhere, so is an isomorphism. Thus restriction induces a
bijection on sections, hence on every Hom set. This is full faithfulness. Empty U or V
cause no exception: the same clopen and rank argument applies to empty schemes. -/
theorem Scheme.fullyFaithful_pullback_finiteEtale_of_henselianRing
    (hstable : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange)
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    letI := hstable
    Nonempty (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).FullyFaithful := by
  classical
  have := hstable
  let F := MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i
  have hbij : ∀ U V, Function.Bijective (F.map : (U ⟶ V) → (F.obj U ⟶ F.obj V)) := by
    intro U V
    let p : U.left ⟶ Y := U.hom
    let q : V.left ⟶ Y := V.hom
    have : IsFinite p := U.prop.1
    have : Etale p := U.prop.2
    have : IsFinite q := V.prop.1
    have : Etale q := V.prop.2
    let p₀ := pullback.snd p i
    let q₀ := pullback.snd q i
    let j := pullback.map q₀ p₀ q p (pullback.fst q i) (pullback.fst p i) i
      (pullback.condition (f := q) (g := i)).symm
      (pullback.condition (f := p) (g := i)).symm
    obtain ⟨hprod, hgraph⟩ := Scheme.finiteEtale_graph_base_change p q i
    change IsPullback j (pullback.snd q₀ p₀) (pullback.snd q p)
      (pullback.fst p i) at hprod
    have hU := (IsPullback.of_hasPullback p i).paste_vert h
    have hP := hprod.paste_vert hU
    have hclU := Scheme.henselian_clopen_restriction I (p ≫ f) (pullback.fst p i)
      (p₀ ≫ f₀) hU
    have hclP := Scheme.henselian_clopen_restriction I (pullback.snd q p ≫ p ≫ f) j
      (pullback.snd q₀ p₀ ≫ p₀ ≫ f₀) hP
    obtain ⟨e, he⟩ := Scheme.finiteEtale_graph_clopen p q
    obtain ⟨e₀, he₀⟩ := Scheme.finiteEtale_graph_clopen p₀ q₀
    let changeBase : {a : U.left ⟶ V.left // a ≫ q = p} →
        {a : (pullback p i) ⟶ (pullback q i) // a ≫ q₀ = p₀} := fun a ↦
      ⟨pullback.lift (pullback.fst p i ≫ a.1) p₀
        (by dsimp [p₀]; simp [Category.assoc, a.2, pullback.condition]),
        by dsimp [q₀]; simp⟩
    have hcompat (a) : (e₀ (changeBase a)).1.carrier = j.base ⁻¹' (e a).1.carrier := by
      rw [he₀, he]
      exact hgraph a.1 a.2
    have hcbinj : Function.Injective changeBase := by
      intro a b hab
      apply e.injective
      apply Subtype.ext
      apply TopologicalSpace.Opens.ext
      apply hclP.1 _ _ ⟨(e a).1.isOpen, (e a).2.1⟩
        ⟨(e b).1.isOpen, (e b).2.1⟩
      exact (hcompat a).symm.trans ((congrArg (fun x ↦ (e₀ x).1.carrier) hab).trans
        (hcompat b))
    have hcbsurj : Function.Surjective changeBase := by
      intro a₀
      obtain ⟨W, hW, hpre⟩ := hclP.2 (e₀ a₀).1.carrier
        ⟨(e₀ a₀).1.isOpen, (e₀ a₀).2.1⟩
      let O : (pullback q p).Opens := ⟨W, hW.1⟩
      have hOpre : j ⁻¹ᵁ O = (e₀ a₀).1 := by
        apply TopologicalSpace.Opens.ext
        exact hpre
      have hiso₀ : IsIso ((j ⁻¹ᵁ O).ι ≫ pullback.snd q₀ p₀) := by
        rw [hOpre]
        exact (e₀ a₀).2.2
      have hiso : IsIso (O.ι ≫ pullback.snd q p) :=
        (rank_one_of_clopen_injective (pullback.snd q p) j (pullback.snd q₀ p₀)
          (pullback.fst p i) hprod hclU.1 O hW.2).mpr hiso₀
      let C : {W : (pullback q p).Opens // IsClosed W.carrier ∧
          IsIso (W.ι ≫ pullback.snd q p)} := ⟨O, hW.2, hiso⟩
      refine ⟨e.symm C, e₀.injective ?_⟩
      apply Subtype.ext
      apply TopologicalSpace.Opens.ext
      change (e₀ (changeBase (e.symm C))).1.carrier = (e₀ a₀).1.carrier
      rw [hcompat, e.apply_symm_apply]
      exact hpre
    constructor
    · intro a b hab
      apply MorphismProperty.Over.Hom.ext
      have hab' : changeBase ⟨a.left, MorphismProperty.Over.w a⟩ =
          changeBase ⟨b.left, MorphismProperty.Over.w b⟩ := by
        apply Subtype.ext
        change (F.map a).left = (F.map b).left
        exact congrArg (fun z : F.obj U ⟶ F.obj V ↦ z.left) hab
      exact congrArg Subtype.val (hcbinj hab')
    · intro a₀
      obtain ⟨a, ha⟩ := hcbsurj ⟨a₀.left, MorphismProperty.Over.w a₀⟩
      refine ⟨MorphismProperty.Over.homMk a.1 a.2, ?_⟩
      apply MorphismProperty.Over.Hom.ext
      change (changeBase a).1 = a₀.left
      exact congrArg Subtype.val ha
  have : F.Faithful := ⟨fun {U V} ↦ (hbij U V).1⟩
  have : F.Full := ⟨fun {U V} ↦ (hbij U V).2⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

end AlgebraicGeometry
