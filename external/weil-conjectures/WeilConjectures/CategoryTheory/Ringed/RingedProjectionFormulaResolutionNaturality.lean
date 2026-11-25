/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Naturality of a comparison characterized on resolving complexes. -/

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem quasiIso_pullback_snd_of_epi
    {A : Type u} [Category.{v} A] [Abelian A]
    {P Q M : CochainComplex A ℤ} (q : P ⟶ M) [Epi q] [QuasiIso q] (p : Q ⟶ M) :
    QuasiIso (pullback.snd q p) := by
  let S : ShortComplex (CochainComplex A ℤ) := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hs : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have hk : (kernel q).Acyclic := hs.acyclic_X₁ inferInstance
  have ht := hs.pullback p
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz (i : ℤ) : IsZero ((kernel q).homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hk i)
  have hm : Mono (HomologicalComplex.homologyMap (pullback.snd q p) n) :=
    (ht.homology_exact₂ n).mono_g ((hz n).eq_of_src _ _)
  have he : Epi (HomologicalComplex.homologyMap (pullback.snd q p) n) :=
    (ht.homology_exact₃ n (n + 1) (by simp)).epi_f ((hz (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Comparisons fixed on every resolving quasi-isomorphism are natural.
Source: the common-resolution argument for flat tensor representatives,
Stacks 07A4 and ProjectionFormulaArrows.
(blueprint: new-lem-weil-pbc-projection-resolution-naturality).
Proof: choose an epimorphic resolving quasi-isomorphism q to the target of f, and resolve
its pullback along f. The composite v to the source is a quasi-isomorphism, since pulling
back an epimorphic quasi-isomorphism preserves its acyclic kernel. Both comparison squares
at v and q are prescribed. Naturality on resolving objects identifies the remaining maps
along the other projection w. The pullback equation w q = v f identifies the two composites.
Cancel the invertible image of v under G. -/
theorem resolutionComparison_naturality
    {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
    (P : ObjectProperty (CochainComplex A ℤ))
    (G T : CochainComplex A ℤ ⥤ B) (b : P.ι ⋙ G ⟶ P.ι ⋙ T)
    (hres : ∀ K, ∃ (W : CochainComplex A ℤ) (_hW : P W) (q : W ⟶ K),
      QuasiIso q ∧ Epi q)
    (hG : ∀ {X Y} (q : X ⟶ Y), QuasiIso q → IsIso (G.map q))
    (e : ∀ K, G.obj K ⟶ T.obj K)
    (he : ∀ K W (hW : P W) (q : W ⟶ K), QuasiIso q →
      G.map q ≫ e K = b.app ⟨W, hW⟩ ≫ T.map q)
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    G.map f ≫ e Y = e X ≫ T.map f := by
  obtain ⟨W, hW, q, hq, hqe⟩ := hres Y
  let := hq
  let := hqe
  obtain ⟨Z, hZ, r, hr, _⟩ := hres (pullback q f)
  let := hr
  let := quasiIso_pullback_snd_of_epi q f
  let v := r ≫ pullback.snd q f
  let w := r ≫ pullback.fst q f
  have hv : QuasiIso v := by dsimp [v]; infer_instance
  have hw : w ≫ q = v ≫ f := by simp [w, v, Category.assoc, pullback.condition]
  let := hG v hv
  have hn := b.naturality (ObjectProperty.homMk (X := ⟨Z, hZ⟩) (Y := ⟨W, hW⟩) w)
  change G.map w ≫ b.app ⟨W, hW⟩ = b.app ⟨Z, hZ⟩ ≫ T.map w at hn
  apply (cancel_epi (G.map v)).1
  calc
    G.map v ≫ (G.map f ≫ e Y) = G.map w ≫ (G.map q ≫ e Y) := by
      rw [← Category.assoc, ← G.map_comp, ← hw, G.map_comp, Category.assoc]
    _ = G.map w ≫ (b.app ⟨W, hW⟩ ≫ T.map q) := by rw [he Y W hW q hq]
    _ = b.app ⟨Z, hZ⟩ ≫ T.map (w ≫ q) := by
      rw [← Category.assoc, hn, Category.assoc, ← T.map_comp]
    _ = b.app ⟨Z, hZ⟩ ≫ T.map (v ≫ f) := by rw [hw]
    _ = G.map v ≫ (e X ≫ T.map f) := by
      rw [T.map_comp, ← Category.assoc, ← he X Z hZ v hv, Category.assoc]

end CategoryTheory
