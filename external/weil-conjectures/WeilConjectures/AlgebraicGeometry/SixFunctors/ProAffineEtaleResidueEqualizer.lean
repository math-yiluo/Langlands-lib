/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! Residue-field equality loci for maps into a pro-affine etale object.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem etale_residue_equalizer
    (X U W : Scheme.{u}) [IsAffine U] (t : U ⟶ X) [Etale t]
    (p q : W ⟶ U) (hpq : p ≫ t = q ≫ t) :
    let E := {x : W | W.fromSpecResidueField x ≫ p = W.fromSpecResidueField x ≫ q}
    IsClopen E ∧ ∀ (V : Scheme.{u}) (f : V ⟶ W),
      Set.range f ⊆ E → f ≫ p = f ≫ q := by
  let c := pullback.lift p q hpq
  let d := pullback.diagonal t
  let e := pullback.fst c d
  have hcons : e ≫ p = e ≫ q := by
    have h := pullback.condition (f := c) (g := d)
    have h₁ := congrArg (fun k ↦ k ≫ pullback.fst t t) h
    have h₂ := congrArg (fun k ↦ k ≫ pullback.snd t t) h
    simp only [c, d, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h₁ h₂
    exact h₁.trans h₂.symm
  have heq : Set.range e = {x : W |
      W.fromSpecResidueField x ≫ p = W.fromSpecResidueField x ≫ q} := by
    ext x
    constructor
    · intro hx
      change W.fromSpecResidueField x ≫ p = W.fromSpecResidueField x ≫ q
      have hr : Set.range (W.fromSpecResidueField x) ⊆ Set.range e := by
        rw [W.range_fromSpecResidueField]
        exact Set.singleton_subset_iff.mpr hx
      let s := IsOpenImmersion.lift e (W.fromSpecResidueField x) hr
      have hs : s ≫ e = W.fromSpecResidueField x := IsOpenImmersion.lift_fac _ _ _
      rw [← hs, Category.assoc, hcons, ← Category.assoc]
    · intro hx
      let s := W.fromSpecResidueField x
      have hs : s ≫ c = (s ≫ p) ≫ d := by
        apply pullback.hom_ext
        · simp [c, d, Category.assoc]
        · simpa only [c, d, Category.assoc, pullback.lift_snd,
            pullback.diagonal_snd, Category.comp_id] using hx.symm
      let k := pullback.lift s (s ≫ p) hs
      refine ⟨k (IsLocalRing.closedPoint (W.residueField x)), ?_⟩
      change (k ≫ e) _ = x
      rw [pullback.lift_fst]
      exact W.fromSpecResidueField_apply _ _
  refine ⟨heq ▸ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩,
    fun V f hf ↦ ?_⟩
  have hr : Set.range f ⊆ Set.range e := hf.trans_eq heq.symm
  let s := IsOpenImmersion.lift e f hr
  have hs : s ≫ e = f := IsOpenImmersion.lift_fac _ _ _
  rw [← hs, Category.assoc, hcons, ← Category.assoc]

/-- The equality locus of two maps into a pro-affine etale object is closed and
saturated under connected components. A map whose image lies in this locus equalizes
those arrows as scheme morphisms, including on nonreduced test schemes. -/
theorem proAffineEtale_residue_equalizer
    (X : Scheme.{u}) (U W : X.ProEt) (hU : proAffineEtale U.hom) (p q : W ⟶ U) :
    let E := {x : W.left | W.left.fromSpecResidueField x ≫ p.left =
      W.left.fromSpecResidueField x ≫ q.left}
    IsClosed E ∧ (∀ x ∈ E, connectedComponent x ⊆ E) ∧
      ∀ (V : X.ProEt) (f : V ⟶ W), Set.range f.left ⊆ E → f ≫ p = f ≫ q := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hU
  have hAff (j : J) : IsAffine (D.obj j) :=
    CategoryTheory.MorphismProperty.ofObjectProperty_top_right_iff.mp (hts j).1.2
  have hEt (j : J) : Etale (t.app j) := (hts j).1.1
  let p' (j : J) := p.left ≫ s.app j
  let q' (j : J) := q.left ≫ s.app j
  have hpq (j : J) : p' j ≫ t.app j = q' j ≫ t.app j := by
    simp only [p', q', Category.assoc, (hts j).2]
    exact (MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm
  have hstage (j : J) := etale_residue_equalizer X (D.obj j) W.left (t.app j)
    (p' j) (q' j) (hpq j)
  let E (j : J) : Set W.left := {x | W.left.fromSpecResidueField x ≫ p' j =
    W.left.fromSpecResidueField x ≫ q' j}
  have heq : {x : W.left | W.left.fromSpecResidueField x ≫ p.left =
      W.left.fromSpecResidueField x ≫ q.left} = ⋂ j, E j := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, E, p', q']
    constructor
    · intro h j
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ s.app j) h
    · intro h
      apply hs.hom_ext
      intro j
      exact (Category.assoc _ _ _).trans ((h j).trans (Category.assoc _ _ _).symm)
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact isClosed_iInter fun j ↦ (hstage j).1.isClosed
  · intro x hx y hy
    rw [heq] at hx ⊢
    simp only [Set.mem_iInter] at hx ⊢
    intro j
    exact isPreconnected_connectedComponent.subset_isClopen (hstage j).1
      ⟨x, mem_connectedComponent, hx j⟩ hy
  · intro V f hf
    apply MorphismProperty.Over.Hom.ext
    apply hs.hom_ext
    intro j
    have hr : Set.range f.left ⊆ E j := by
      intro x hx
      have hm := hf hx
      rw [heq] at hm
      exact Set.mem_iInter.mp hm j
    change (f.left ≫ p.left) ≫ s.app j = (f.left ≫ q.left) ≫ s.app j
    simpa only [p', q', Category.assoc] using (hstage j).2 V.left f.left hr

end AlgebraicGeometry
