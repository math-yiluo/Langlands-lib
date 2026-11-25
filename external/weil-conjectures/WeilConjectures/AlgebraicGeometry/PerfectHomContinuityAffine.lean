/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityOn
import WeilConjectures.AlgebraicGeometry.AffinePerfectHomPresentation
import WeilConjectures.AlgebraicGeometry.AffinePerfectHomColimit
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Affine-open base case for continuity of perfect Hom
Source: Stacks Project, perfect.tex, Tag 09RE, affine case of lemma-descend-homomorphisms.
(blueprint: lem-pc-perfect-hom-continuity-affine).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The affine module Hom-colimit comparison implies the two continuity clauses.
The proof uses a representative at a common upper bound for existence, and
functoriality after eventual equality for uniqueness. -/
private theorem affine_perfect_hom_continuity_pair
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) :
    (∀ (j₀ : I) (hij₀ : i ≤ j₀)
      (φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      ∃ (j : I) (hj₀j : j₀ ≤ j)
        (f : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj P ⟶
          (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj Q),
        perfectLimitMap R c s (hij₀.trans hj₀j) f = φ) ∧
    (∀ (j : I) (hij : i ≤ j)
      (a b : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q),
      perfectLimitMap R c s hij a = perfectLimitMap R c s hij b →
      ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
        perfectStageMap R s hij (hjk.trans hkl) a =
          perfectStageMap R s hij (hjk.trans hkl) b) := by
  let : ∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    fun A ↦ HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨F, E, K, hE, hK, H, ident, d, e, stage, limit,
    htransition, hcanonical, hstage, hlimit⟩ :=
    exists_affinePerfectHomPresentation R c hc i Y s P Q hP hQ
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  have : Nonempty (Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    ⟨⟨⟨i, le_rfl⟩, le_rfl⟩⟩
  have : IsDirected (Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (· ≤ ·) :=
    ⟨fun j k ↦ by
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
      exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  have hbij := CochainComplex.affine_perfect_hom_colimit F ⟨i, le_rfl⟩
    E K hE hK H ident htransition d e hcanonical
  have hdesc : Function.Bijective (colimit.desc H d) := by
    constructor
    · intro x y hxy
      exact hbij.1 (congrArg e hxy)
    · intro y
      obtain ⟨x, hx⟩ := hbij.2 (e y)
      exact ⟨x, e.injective hx⟩
  have hfac (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (f : H.obj j) :
      colimit.desc H d (colimit.ι H j f) = d.ι.app j f := by
    exact ConcreteCategory.congr_hom (colimit.ι_desc d j) f
  constructor
  · intro j₀ hij₀ φ
    obtain ⟨x, hx⟩ := hdesc.2 (limit.symm φ)
    obtain ⟨j, f, hf⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit H) x
    obtain ⟨k, hjk, hj₀k⟩ := exists_ge_ge j.val.val j₀
    let k' : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) := ⟨⟨k, hij₀.trans hj₀k⟩, hij₀.trans hj₀k⟩
    refine ⟨k, hj₀k, stage k' (H.map (homOfLE hjk) f), ?_⟩
    calc
      _ = limit (d.ι.app k' (H.map (homOfLE hjk) f)) := (hlimit k' _).symm
      _ = limit (d.ι.app j f) :=
        congrArg limit (ConcreteCategory.congr_hom (d.w (homOfLE hjk)) f)
      _ = limit (limit.symm φ) := congrArg limit
        ((hfac j f).symm.trans ((congrArg (fun z ↦ colimit.desc H d z) hf).trans hx))
      _ = φ := limit.apply_symm_apply φ
  · intro j hij a b hab
    let j' : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) := ⟨⟨j, hij⟩, hij⟩
    let a' := (stage j').symm a
    let b' := (stage j').symm b
    have heq : colimit.ι H j' a' = colimit.ι H j' b' := by
      apply hdesc.1
      rw [hfac, hfac]
      apply limit.injective
      simpa only [hlimit, a', b', Equiv.apply_symm_apply] using hab
    obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.colimit_eq_iff H).1 heq
    have hjk : j' ≤ k := leOfHom f
    have hfg' : H.map (homOfLE hjk) a' = H.map (homOfLE hjk) b' := by
      simpa only [Subsingleton.elim f (homOfLE hjk),
        Subsingleton.elim g (homOfLE hjk)] using hfg
    refine ⟨k.val.val, hjk, ?_⟩
    intro l hkl
    let l' : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) :=
      ⟨⟨l, k.val.property.trans hkl⟩, k.property.trans hkl⟩
    have hkl' : k ≤ l' := hkl
    have hl : H.map (homOfLE (hjk.trans hkl')) a' =
        H.map (homOfLE (hjk.trans hkl')) b' := by
      have he := congrArg (H.map (homOfLE (show k ≤ l' from hkl))) hfg'
      simpa only [← CategoryTheory.types_comp_apply, ← Functor.map_comp,
        homOfLE_comp] using he
    have he := congrArg (stage l') hl
    simpa only [hstage, a', b', Equiv.apply_symm_apply] using he

/-- The open-local continuity condition holds on affine opens.
Source: Stacks Project, perfect.tex, Tag 09RE, affine case.
(blueprint: lem-pc-perfect-hom-continuity-affine).

Proof: Let t : Y → X present the affine open U. The open immersion identifies Y
with U, so Y is affine. Write Y = Spec B_i. Its base changes have rings
B_j = B_i ⊗_{R_i} R_j and B = B_i ⊗_{R_i} c.pt; tensor extension preserves the
ring colimit. Perfect complexes have quasi-coherent cohomology. Apply
`perfect_iff_affine_bounded_projective` and the affine quasi-coherent derived
equivalence to represent both by bounded finite-projective B_i-complexes E and K.
Their terms are projective, hence flat, so ordinary tensor computes all derived
pullbacks. The termwise tilde comparison identifies chain maps and homotopies
with sheaf-derived maps, and its naturality identifies scalar-extension transport
with the counit-pinned composition conjugations in `perfectStageMap` and
`perfectLimitMap`. Apply `affine_perfect_hom_colimit` to this identified diagram.
The tail above any j₀ ≥ i is directed and cofinal: a common upper bound of j₀ and
any stage supplies cofinality. Thus bijectivity gives a representative above j₀.
If two images agree, injectivity and the filtered-set colimit equality criterion
give equality at a common later stage k. Composition coherence transports that
equality to every l ≥ k. This proves both clauses for every perfect pair on Y,
as required by `PerfectHomContinuityOn`. The empty affine scheme is covered as
well: its derived category is zero, so both conclusions also hold directly. -/
theorem perfect_hom_continuity_affine
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    PerfectHomContinuityOn R c i X s U := by
  intro Y t _ ht sY _ _ _ _ _ P Q hP hQ
  have : IsAffine t.opensRange.toScheme := ht.symm ▸ hU
  have : IsAffine Y := IsAffine.of_isIso t.isoOpensRange.hom
  exact affine_perfect_hom_continuity_pair R c hc i Y sY P Q hP hQ

end AlgebraicGeometry
