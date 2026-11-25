/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedEtaleLocal
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Limits

/-!
# Finite étale morphisms split étale locally

Source: Stacks Project, Etale Morphisms, Lemma 04HN (lemma-finite-etale-etale-local)
(blueprint: lem-weil-pbc-finite-etale-etale-local-split)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- A coproduct cofan covers all points, via the homeomorphism for the chosen coproduct. -/
private theorem cofan_cover {Z : Scheme.{u}} {J : Type u} (V : J → Scheme.{u})
    (ι : ∀ j, V j ⟶ Z) (hc : Nonempty (IsColimit (Cofan.mk Z ι))) (z : Z) :
    ∃ j, ∃ v : V j, (ι j).base v = z := by
  have : IsIso (Sigma.desc ι) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Z ι)).mp hc
  obtain ⟨y, rfl⟩ := (Sigma.desc ι).surjective z
  obtain ⟨⟨j, v⟩, rfl⟩ := (sigmaMk V).surjective y
  refine ⟨j, v, ?_⟩
  simp [sigmaMk_mk, ← Scheme.Hom.comp_apply]

/-- Points in distinct summands cannot have the same image in a coproduct cofan. -/
private theorem cofan_index_eq {Z : Scheme.{u}} {J : Type u} (V : J → Scheme.{u})
    (ι : ∀ j, V j ⟶ Z) (hc : Nonempty (IsColimit (Cofan.mk Z ι)))
    {j k : J} (v : V j) (w : V k) (h : (ι j).base v = (ι k).base w) : j = k := by
  have : IsIso (Sigma.desc ι) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Z ι)).mp hc
  have he : (Sigma.ι V j).base v = (Sigma.ι V k).base w := by
    apply (Sigma.desc ι).injective
    simpa [← Scheme.Hom.comp_apply] using h
  exact congrArg Sigma.fst ((sigmaι_eq_iff V j k v w).mp he)

/-- Intersect each clopen or its complement according to its membership at the given point. -/
private theorem exists_uniform_clopen_neighbourhood {Z : Scheme.{u}} {J : Type u}
    [Finite J] (T : J → Set Z) (ho : ∀ j, IsOpen (T j)) (hc : ∀ j, IsClosed (T j))
    (z : Z) : ∃ W : Z.Opens, z ∈ W ∧ ∀ j, ∀ y ∈ W, y ∈ T j ↔ z ∈ T j := by
  classical
  let A : J → Set Z := fun j ↦ if z ∈ T j then T j else (T j)ᶜ
  have hA : ∀ j, IsOpen (A j) := by
    intro j
    dsimp [A]
    split_ifs
    · exact ho j
    · exact (hc j).isOpen_compl
  let W : Z.Opens := ⟨⋂ j, A j, isOpen_iInter_of_finite hA⟩
  refine ⟨W, ?_, ?_⟩
  · change z ∈ ⋂ j, A j
    apply Set.mem_iInter.mpr
    intro j
    dsimp [A]
    split_ifs with hj
    · exact hj
    · exact hj
  · intro j y hy
    have hj : y ∈ A j := Set.mem_iInter.mp hy j
    dsimp [A] at hj
    split_ifs at hj with hz
    · exact iff_of_true hj hz
    · exact iff_of_false hj hz

/-- Restrict a clopen coproduct to a neighbourhood on which all component-image memberships
are constant. The surviving components cover the pullback, remain disjoint, and their maps
to the neighbourhood are surjective open immersions, hence isomorphisms. -/
private theorem split_clopen_baseChange {Z U : Scheme.{u}} (p : Z ⟶ U)
    {J : Type u} (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ Z)
    (hc : Nonempty (IsColimit (Cofan.mk Z ι)))
    [∀ j, IsOpenImmersion (ι j)]
    [∀ j, IsOpenImmersion (ι j ≫ p)] (u : U) (W : U.Opens)
    (hW : ∀ j, ∀ y ∈ W, y ∈ Set.range (ι j ≫ p).base ↔
      u ∈ Set.range (ι j ≫ p).base) :
    let K := {j : J // u ∈ Set.range (ι j ≫ p).base}
    let a := fun j : K ↦ pullback.snd (ι j.val) (pullback.fst p W.ι)
    Nonempty (IsColimit (Cofan.mk (pullback p W.ι) a)) ∧
      (∀ j : K, IsIso (a j ≫ pullback.snd p W.ι)) := by
  classical
  dsimp only
  let K := {j : J // u ∈ Set.range (ι j ≫ p).base}
  let a := fun j : K ↦ pullback.snd (ι j.val) (pullback.fst p W.ι)
  have ha (j : K) : Set.range (a j).base =
      (pullback.fst p W.ι).base ⁻¹' Set.range (ι j.val).base :=
    Scheme.Pullback.range_snd _ _
  have hfac (j : K) :
      (a j ≫ pullback.snd p W.ι) ≫ W.ι =
        pullback.fst (ι j.val) (pullback.fst p W.ι) ≫ (ι j.val ≫ p) := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      ← pullback.condition, Category.assoc]
  have hopen (j : K) : IsOpenImmersion (a j ≫ pullback.snd p W.ι) := by
    have : IsOpenImmersion ((a j ≫ pullback.snd p W.ι) ≫ W.ι) := by
      rw [hfac j]
      infer_instance
    exact IsOpenImmersion.of_comp _ W.ι
  have hcov : ⨆ j : K, (a j).opensRange = ⊤ := by
    apply top_unique
    intro t ht
    obtain ⟨j, v, hv⟩ := cofan_cover V ι hc ((pullback.fst p W.ι).base t)
    have hj : u ∈ Set.range (ι j ≫ p).base := by
      apply (hW j ((pullback.snd p W.ι).base t).val
        ((pullback.snd p W.ι).base t).property).mp
      refine ⟨v, ?_⟩
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hv]
      exact congrArg (fun h : pullback p W.ι ⟶ U ↦ h.base t) (pullback.condition)
    have hat : t ∈ (a ⟨j, hj⟩).opensRange := by
      change t ∈ Set.range (a ⟨j, hj⟩).base
      rw [ha]
      exact ⟨v, hv⟩
    exact (le_iSup (fun j : K ↦ (a j).opensRange) ⟨j, hj⟩) hat
  have hdisj : Pairwise (fun j k : K ↦ Disjoint (a j).opensRange (a k).opensRange) := by
    intro j k hjk
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro t ht
    rcases ht with ⟨htj, htk⟩
    change t ∈ Set.range (a j).base at htj
    change t ∈ Set.range (a k).base at htk
    rw [ha] at htj htk
    obtain ⟨v, hv⟩ := htj
    obtain ⟨w, hw⟩ := htk
    exact (hjk (Subtype.ext (cofan_index_eq V ι hc v w (hv.trans hw.symm)))).elim
  refine ⟨nonempty_isColimit_cofanMk_of a hcov hdisj, ?_⟩
  intro j
  let : IsOpenImmersion (a j ≫ pullback.snd p W.ι) := hopen j
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_unique
  intro w hw
  obtain ⟨v, hv⟩ := (hW j.val w.val w.property).mpr j.property
  have hv' : p.base ((ι j.val).base v) = W.ι.base w := hv
  obtain ⟨t, ht, htw⟩ := Scheme.Pullback.exists_preimage_pullback
    ((ι j.val).base v) w hv'
  have hat : t ∈ Set.range (a j).base := by
    rw [ha]
    exact ⟨v, ht.symm⟩
  obtain ⟨s, hs⟩ := hat
  refine ⟨s, ?_⟩
  change (pullback.snd p W.ι).base ((a j).base s) = w
  rw [hs]
  exact htw

/-- A finite étale morphism `f : Y ⟶ X` is, around every point `x` of its target, a finite
disjoint union of copies of an étale neighbourhood: there are an étale `g : U ⟶ X`, a point
`u` over `x`, a finite `J` and open-and-closed pieces `ι j : V j ⟶ Y ×_X U` exhibiting
`Y ×_X U` as their coproduct (`IsColimit (Cofan.mk _ ι)`, the split-cover spelling of
lem-weil-pbc-direct-image-split-cover-product; the pieces are then pairwise disjoint and
cover), each mapping isomorphically to `U` under `pullback.snd`. Stacks Lemma 04HN
(blueprint: lem-weil-pbc-finite-etale-etale-local-split).

Proof (the five steps of the node):
1. An étale morphism is unramified; apply lem-weil-pbc-finite-unramified-etale-local
   (Stacks 04HJ) to `f` and `x`: an étale `g : U → X`, `u ↦ x`, a finite `J₀` and pairwise
   disjoint open and closed `V_j ⊆ Y_U` covering `Y_U` with each `p_j : V_j → U` a closed
   immersion.
2. `pr₂ : Y_U → U` is étale (base change), the inclusion of `V_j` is an open immersion, so
   `p_j` is an étale closed immersion, hence an open immersion
   (lem-weil-pbc-etale-closed-immersion-open) onto an open and closed `T_j ⊆ U`.
3. Shrink: `J = {j | u ∈ T_j}`, `U' = ⋂_{j ∈ J} T_j \ ⋃_{j ∉ J} T_j`, open with `u ∈ U'`;
   `g' = g ∘ ι` is étale with `g'(u) = x`.
4. Restrict the coproduct to the iterated pullback over `U'`, using pullback ranges
   to prove coverage and disjointness; identify it with `Y ×_X U'` by pullback pasting.
5. `V'_j = V_j ∩ pr₂⁻¹(U')` is empty for `j ∉ J` and maps isomorphically onto `U'` for
   `j ∈ J`; so `Y ×_X U' = ∐_{j ∈ J} V'_j` as claimed (`J = ∅` allowed when `Y_x = ∅`). -/
theorem finite_etale_etale_local_split {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (J : Type u) (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ pullback f g),
        Finite J ∧
        Nonempty (IsColimit (Cofan.mk (pullback f g) ι)) ∧
        (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) ∧
        (∀ j : J, ∃ e : V j ≅ U, e.hom = ι j ≫ pullback.snd f g) := by
  classical
  obtain ⟨U, g, u, hg, hu, J, V, ι, hJ, hcol, hι, hp⟩ :=
    exists_etale_closed_immersion_decomposition_of_finite_unramified f x
  let : Etale g := hg
  let : Finite J := hJ
  let (j : J) : IsOpenImmersion (ι j) := (hι j).1
  let (j : J) : IsClosedImmersion (ι j) := (hι j).2
  let (j : J) : IsClosedImmersion (ι j ≫ pullback.snd f g) := hp j
  have hopen (j : J) : IsOpenImmersion (ι j ≫ pullback.snd f g) :=
    IsOpenImmersion.of_flat_of_mono _
  let (j : J) : IsOpenImmersion (ι j ≫ pullback.snd f g) := hopen j
  obtain ⟨W, huW, hW⟩ := exists_uniform_clopen_neighbourhood
    (fun j ↦ Set.range (ι j ≫ pullback.snd f g).base)
    (fun j ↦ (ι j ≫ pullback.snd f g).isOpenEmbedding.isOpen_range)
    (fun j ↦ (ι j ≫ pullback.snd f g).isClosedEmbedding.isClosed_range) u
  let K := {j : J // u ∈ Set.range (ι j ≫ pullback.snd f g).base}
  let D : K → Scheme.{u} :=
    fun j ↦ pullback (ι j.val) (pullback.fst (pullback.snd f g) W.ι)
  let a : ∀ j : K, D j ⟶ pullback (pullback.snd f g) W.ι :=
    fun j ↦ pullback.snd (ι j.val) (pullback.fst (pullback.snd f g) W.ι)
  obtain ⟨hcW, hiW⟩ := split_clopen_baseChange (pullback.snd f g) V ι hcol u W hW
  let e := pullbackLeftPullbackSndIso f g W.ι
  let b : ∀ j : K, D j ⟶ pullback f (W.ι ≫ g) := fun j ↦ a j ≫ e.hom
  refine ⟨W.toScheme, W.ι ≫ g, ⟨u, huW⟩, inferInstance, ?_, K, D, b,
    inferInstance, ?_, ?_, ?_⟩
  · exact hu
  · refine ⟨IsColimit.ofIsoColimit hcW.some ?_⟩
    exact Cofan.ext e (fun j ↦ rfl)
  · intro j
    exact ⟨inferInstance, inferInstance⟩
  · intro j
    have : IsIso (a j ≫ pullback.snd (pullback.snd f g) W.ι) := hiW j
    have hb : b j ≫ pullback.snd f (W.ι ≫ g) =
        a j ≫ pullback.snd (pullback.snd f g) W.ι := by
      simp [b, e]
    have : IsIso (b j ≫ pullback.snd f (W.ι ≫ g)) := hb ▸ ‹_›
    exact ⟨asIso (b j ≫ pullback.snd f (W.ι ≫ g)), rfl⟩

end AlgebraicGeometry
