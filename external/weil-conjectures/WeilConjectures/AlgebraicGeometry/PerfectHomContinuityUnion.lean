/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityOn
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisComparison
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Mayer--Vietoris gluing for continuity of perfect Hom
Source: Stacks Project, perfect.tex, Tag 09RE, quasi-compact-open induction step.
(blueprint: lem-pc-perfect-hom-continuity-union).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Continuity is preserved by adjoining an affine open, provided it also holds
on the intersection. The hypotheses are continuity for all perfect pairs, hence
supply the adjacent shifts in the long exact Hom sequence.
Source: Stacks Project, perfect.tex, Tag 09RE, Mayer--Vietoris step.
(blueprint: lem-pc-perfect-hom-continuity-union).

Proof: Let t : Y → X present U ∪ V. The preimages of U and V cover Y and their
intersection presents U ∩ V. Quasi-compactness of U and affineness of V make
both preimages quasi-compact; quasi-separatedness makes their intersection
quasi-compact. At every ring stage and at the colimit apply the derived
Mayer--Vietoris triangle to Q, whose cohomology is quasi-coherent because Q is
perfect. Apply Hom(P, -[n]). The open-immersion derived adjunction identifies
its local terms with Hom between the restrictions of P and Q[n]. Restriction
preserves perfectness, including all shifts. The given three open-local
conditions identify their filtered Hom colimits with the limit Hom groups in
all degrees. For each affine transition h, use
`schemeDerived_mayerVietoris_directImage` to compare the direct image of the
source triangle with the triangle of Rh_*Lh^*Q. Its natural boundary and the
adjunction unit Q → Rh_*Lh^*Q give the comparison from the target triangle.
Apply Hom(P, -[n]) and the derived adjunction to obtain a morphism of long exact
Hom sequences. Identify its local maps by open restriction and its middle map
with the canonical transport using the counit-pinned composition comparisons.
These identifications are necessary; the existence of a triangle alone does
not establish compatibility of the boundary maps.
Filtered colimits of abelian groups preserve exactness. The five lemma around
Hom(P, Q[n]) therefore gives a bijection at Y. Cofinality of every tail gives
the first clause of the condition; injectivity and the filtered-set equality
criterion give equality at a later stage, and functoriality propagates it along
the entire later tail, giving the second. These arguments also apply when U,
V or their intersection is empty; the corresponding Hom groups are zero. -/
theorem perfect_hom_continuity_union
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (hcontU : PerfectHomContinuityOn R c i X s U)
    (hcontV : PerfectHomContinuityOn R c i X s V)
    (hcontUV : PerfectHomContinuityOn R c i X s (U ⊓ V)) :
    PerfectHomContinuityOn R c i X s (U ⊔ V) := by
  by_cases hUV : U ≤ V
  · simpa only [sup_eq_right.mpr hUV] using hcontV
  by_cases hVU : V ≤ U
  · simpa only [sup_eq_left.mpr hVU] using hcontU
  intro Y t _ ht s' hs' _ _ _ _ P Q hP hQ
  obtain ⟨H, d, ⟨hd⟩, ident, htransition, A, B, φ, a, b,
    hA, hB, h0, h1, h3, h4, hcanonical⟩ :=
    perfect_hom_mayerVietoris_comparison R c i X s U V hU hV
      hcontU hcontV hcontUV Y t ht s' hs' P Q hP hQ
  have : IsIso (ComposableArrows.app' φ 0) := h0
  have : IsIso (ComposableArrows.app' φ 1) := h1
  have : IsIso (ComposableArrows.app' φ 3) := h3
  have : IsIso (ComposableArrows.app' φ 4) := h4
  have : IsIso (ComposableArrows.app' φ 2) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hA hB φ
      inferInstance h1 h3 inferInstance
  let m : d.pt → _ := fun x ↦ b ((ComposableArrows.app' φ 2) (a x))
  have hmid : Function.Bijective (ComposableArrows.app' φ 2) :=
    ConcreteCategory.bijective_of_isIso _
  have hm : Function.Bijective m := b.bijective.comp (hmid.comp a.bijective)
  have hpin (j : Set.Ici i) (f : H.obj j) :
      m (d.ι.app j f) = perfectLimitMap R c s' j.property (ident j f) :=
    hcanonical j f
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  constructor
  · intro j₀ hij₀ f
    obtain ⟨x, hx⟩ := hm.surjective f
    obtain ⟨j, g, hg⟩ := Types.jointly_surjective_of_isColimit hd x
    obtain ⟨k, hjk, hj₀k⟩ := exists_ge_ge j.val j₀
    let k' : Set.Ici i := ⟨k, j.property.trans hjk⟩
    refine ⟨k, hj₀k, ident k' (H.map (homOfLE hjk) g), ?_⟩
    rw [← hpin k']
    have hw := congrArg (fun z ↦ m z)
      (ConcreteCategory.congr_hom (d.w (homOfLE hjk : j ⟶ k')) g)
    exact hw.trans ((congrArg m hg).trans hx)
  · intro j hij f g hfg
    let j' : Set.Ici i := ⟨j, hij⟩
    have heq : d.ι.app j' ((ident j').symm f) =
        d.ι.app j' ((ident j').symm g) := by
      apply hm.injective
      simpa only [hpin, Equiv.apply_symm_apply] using hfg
    obtain ⟨k, hjk, hk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hd _ _).1 heq
    refine ⟨k.val, leOfHom hjk, ?_⟩
    intro l hkl
    let l' : Set.Ici i := ⟨l, k.property.trans hkl⟩
    have hl := congrArg (fun z ↦ H.map (homOfLE hkl : k ⟶ l') z) hk
    have hmaps : H.map (homOfLE hkl : k ⟶ l') ∘ H.map hjk =
        H.map (homOfLE ((leOfHom hjk).trans hkl) : j' ⟶ l') := by
      funext z
      change H.map (homOfLE hkl) (H.map hjk z) = _
      rw [← types_comp_apply, ← H.map_comp]
      rfl
    have hl' : H.map (homOfLE ((leOfHom hjk).trans hkl) : j' ⟶ l')
        ((ident j').symm f) =
      H.map (homOfLE ((leOfHom hjk).trans hkl) : j' ⟶ l')
        ((ident j').symm g) := by
      change (H.map (homOfLE hkl : k ⟶ l') ∘ H.map hjk) _ =
        (H.map (homOfLE hkl : k ⟶ l') ∘ H.map hjk) _ at hl
      rw [hmaps] at hl
      exact hl
    have he := congrArg (ident l') hl'
    simpa only [htransition, Equiv.apply_symm_apply] using he

end AlgebraicGeometry
