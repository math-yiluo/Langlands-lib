/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.CategoryBaseChange
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.Rat

/-!
# The compactification category and base change

Source: blueprint, sec-nagata-compactification/sk-prop-nagata-sketch-comp-category,
remark-base-change-compactification--1 (blueprint: remark-base-change-compactification--1).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Compactification

set_option linter.unusedVariables false in
/-- Source: blueprint sec-nagata-compactification/sk-prop-nagata-sketch-comp-category,
remark-base-change-compactification--1 (blueprint: remark-base-change-compactification--1).

Proof plan (the eleven steps of the node). Refinements are proper by
lemma-nagata-proper-to-separated-target and compose by proper composition. Nagata's theorem
(theorem-nagata-s-compactification-theorem--1) supplies an object. For two objects use the image of
their graph in the fibre product: the ambient product is proper, and the graph is a quasi-compact
immersion by separatedness and open-immersion base change. The immersion-compactification
lemmas make its image a compactification with dense open, and its two projections are
refinements. Iterate for a finite family, including the empty family by nonemptiness.
For parallel maps take the inverse image of the target's relative diagonal. This is closed;
it contains X, and its inverse image over X is X, so the induced map from X is the base
change of the original quasi-compact open immersion. This compactification equalizes the
maps. These properties give cofilteredness.
Base change preserves the open and proper maps and refinement equations, and the universal
property of fibre products gives preservation of identities, composites and equalities.
The image universal property (lemma-nagata-scheme-image-universal) gives the comparison
closed immersion from the image formed after base change to the pulled-back image, over
both projections. If the base change is flat, lemma-nagata-dense-flat-pullback preserves
density of the quasi-compact, quasi-separated open immersion; its zero kernel forces the
comparison closed immersion to be an isomorphism. The same argument preserves density for
any dense compactification under flat base change. Finally, density fails for arbitrary
base change: take X = D(t) in S = Spec K[t], ambient S, and base change t = 0 to Spec K.
Localization K[t] → K[t,t⁻¹] is injective on principal opens, whereas after this base change
the source is empty and the ambient scheme is Spec K, so the structural map K → 0 is not
injective. This supplies the existential counterexample, with a qcqs base and separated
finite-type source map. -/
theorem compactificationCategory_properties {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (Compactification f) ∧
    (∀ c : Compactification f, QuasiCompact c.i) ∧
    (∀ c d : Compactification f,
      (inf c d).Z = (graph c d).image ∧
      IsSchemeTheoreticallyDominant (inf c d).i ∧
      Nonempty ((inf c d) ⟶ c) ∧ Nonempty ((inf c d) ⟶ d)) ∧
    (∀ (I : Type v) [Finite I] (c : I → Compactification f),
      ∃ e : Compactification f, ∀ i : I, Nonempty (e ⟶ c i)) ∧
    (∀ (c d : Compactification f) (r s : c ⟶ d),
      ∃ (e : Compactification f) (h : e ⟶ c), h ≫ r = h ≫ s) ∧
    IsCofiltered (Compactification f) ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ S),
      (∀ c : Compactification f, QuasiCompact (c.baseChange t).i) ∧
      (∀ (c d : Compactification f) (r : c ⟶ d),
        IsProper (r.baseChange t).hom) ∧
      (∀ (c d : Compactification f) (e : Compactification f)
          (r : e ⟶ c) (s : e ⟶ d),
        Nonempty ((baseChangeFunctor t).obj e ⟶ (baseChangeFunctor t).obj c) ∧
        Nonempty ((baseChangeFunctor t).obj e ⟶ (baseChangeFunctor t).obj d)) ∧
      (∀ (c d e : Compactification f) (r s : c ⟶ d) (h : e ⟶ c),
        h ≫ r = h ≫ s →
          (baseChangeFunctor t).map h ≫ (baseChangeFunctor t).map r =
            (baseChangeFunctor t).map h ≫ (baseChangeFunctor t).map s) ∧
      (∀ c d : Compactification f,
        IsClosedImmersion (infBaseChange c d t).hom ∧
        (infBaseChange c d t).comp ((infFst c d).baseChange t) =
          infFst (c.baseChange t) (d.baseChange t) ∧
        (infBaseChange c d t).comp ((infSnd c d).baseChange t) =
          infSnd (c.baseChange t) (d.baseChange t) ∧
        (Flat t → IsIso (infBaseChange c d t).hom)) ∧
      (Flat t → ∀ c : Compactification f,
        IsSchemeTheoreticallyDominant c.i →
          IsSchemeTheoreticallyDominant (c.baseChange t).i)) ∧
    (∃ (X₀ S₀ T₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (t₀ : T₀ ⟶ S₀)
        (c₀ : Compactification f₀),
      CompactSpace S₀ ∧ QuasiSeparatedSpace S₀ ∧ IsSeparated f₀ ∧
      LocallyOfFiniteType f₀ ∧ QuasiCompact f₀ ∧ QuasiCompact c₀.i ∧
      IsSchemeTheoreticallyDominant c₀.i ∧
      ¬ IsSchemeTheoreticallyDominant (c₀.baseChange t₀).i) := by
  classical
  refine ⟨inferInstance, fun c ↦ c.quasiCompact_openImmersion inferInstance,
    ?_, ?_, ?_, inferInstance, ?_, ?_⟩
  · intro c d
    exact ⟨inf_Z c d, isSchemeTheoreticallyDominant_inf_i c d, ⟨infFst c d⟩, ⟨infSnd c d⟩⟩
  · intro I _ c
    let := Fintype.ofFinite I
    obtain ⟨e, he⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image c)
    exact ⟨e, fun i ↦ he (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  · intro c d r s
    let a : c.Z ⟶ pullback d.g d.g :=
      pullback.lift r.hom s.hom (by rw [r.hom_g, s.hom_g])
    let E := pullback a (pullback.diagonal d.g)
    let k : E ⟶ c.Z := pullback.fst a (pullback.diagonal d.g)
    have : IsClosedImmersion k := inferInstance
    let j : X ⟶ E := pullback.lift c.i d.i (by
      apply pullback.hom_ext <;> simp [a, r.i_hom, s.i_hom])
    have hj : j ≫ k = c.i := pullback.lift_fst _ _ _
    have hsq : IsPullback (𝟙 X) j c.i k :=
      IsPullback.of_horiz_isIso_mono ⟨by simpa using hj.symm⟩
    have : IsOpenImmersion j :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq c.isOpenImmersion
    let e : Compactification f :=
      { Z := E
        g := k ≫ c.g
        i := j
        comm := by rw [← Category.assoc, hj, ← c.comm]
        isProper := inferInstance
        isOpenImmersion := inferInstance }
    let h : e ⟶ c := { hom := k, i_hom := hj, hom_g := rfl }
    refine ⟨e, h, ?_⟩
    apply Refinement.ext
    change k ≫ r.hom = k ≫ s.hom
    have hk := pullback.condition (f := a) (g := pullback.diagonal d.g)
    have hfst := congrArg (fun q ↦ q ≫ pullback.fst d.g d.g) hk
    have hsnd := congrArg (fun q ↦ q ≫ pullback.snd d.g d.g) hk
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at hfst hsnd
    simpa [a, k] using hfst.trans hsnd.symm
  · intro T t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c
      exact (c.baseChange t).quasiCompact_openImmersion inferInstance
    · intro c d r
      infer_instance
    · intro c d e r s
      exact ⟨⟨(baseChangeFunctor t).map r⟩, ⟨(baseChangeFunctor t).map s⟩⟩
    · intro c d e r s h hh
      rw [← Functor.map_comp, ← Functor.map_comp, hh]
    · intro c d
      refine ⟨inferInstance, infBaseChange_comp_infFst c d t,
        infBaseChange_comp_infSnd c d t, ?_⟩
      intro ht
      have := ht
      infer_instance
    · intro ht c hc
      have := ht
      have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
      exact isSchemeTheoreticallyDominant_i_baseChange c t hc
  · let R := Polynomial (ULift.{u} ℚ)
    let S₀ : Scheme.{u} := Spec (CommRingCat.of R)
    let U : S₀.Opens := PrimeSpectrum.basicOpen (Polynomial.X : R)
    have : IsAffine U := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) (Polynomial.X : R)
    have : QuasiCompact U.ι := inferInstance
    have hU : (U : Set S₀).Nonempty := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      exact Polynomial.X_ne_zero
    have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hU)
    have : IsSchemeTheoreticallyDominant U.ι :=
      IsSchemeTheoreticallyDominant.of_isDominant U.ι
    let p : S₀ := ⟨RingHom.ker (Polynomial.evalRingHom (0 : ULift.{u} ℚ)),
      RingHom.ker_isPrime _⟩
    have hp : p ∉ U := by
      change ¬ Polynomial.X ∉ RingHom.ker (Polynomial.evalRingHom (0 : ULift.{u} ℚ))
      simp
    let T₀ := Spec (S₀.residueField p)
    let t : T₀ ⟶ S₀ := S₀.fromSpecResidueField p
    let c := ofIsOpenImmersion U.ι
    have : QuasiCompact c.i := ‹QuasiCompact U.ι›
    have : IsSchemeTheoreticallyDominant c.i := ‹IsSchemeTheoreticallyDominant U.ι›
    refine ⟨U, S₀, T₀, U.ι, t, c, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro hc
    have := hc
    have : QuasiCompact (c.baseChange t).i :=
      (c.baseChange t).quasiCompact_openImmersion inferInstance
    have : IsIso (c.baseChange t).g := by
      change IsIso (pullback.snd (𝟙 S₀) t)
      infer_instance
    have : IsDominant (pullback.snd U.ι t) := by
      rw [(c.baseChange t).comm]
      infer_instance
    obtain ⟨z⟩ := (pullback.snd U.ι t).denseRange.nonempty_iff.mpr inferInstance
    apply hp
    have hz := congrArg (fun k ↦ k z) (pullback.condition (f := U.ι) (g := t))
    have hz' : U.ι (pullback.fst U.ι t z) = p := by
      change U.ι (pullback.fst U.ι t z) = t (pullback.snd U.ι t z) at hz
      exact hz.trans (S₀.fromSpecResidueField_apply p _)
    rw [← hz']
    exact (pullback.fst U.ι t z).property

end AlgebraicGeometry.Compactification
