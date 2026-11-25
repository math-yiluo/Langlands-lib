/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.Galois.Basic
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition

/-!
# Finite Galois descent for sections of an etale sheaf

## References

* Stacks Project, Etale Cohomology, Tag 04JM, finite Galois descent argument

## Implementation details

`Spec E ⟶ Spec L` is an étale cover, and the Galois tensor decomposition identifies the two
restrictions to its self-intersection with the constant family and the family of Galois
pullbacks; the sheaf condition then identifies sections with invariant sections.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- For a finite Galois extension `E/L`, pullback from `Spec L` to `Spec E` identifies
the sections of any sheaf of sets on the small etale site of `Spec L` with the
sections fixed by every `L`-automorphism of `E`. -/
theorem finiteGaloisSectionsDescent
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E]
    (F : Sheaf (Spec (.of L)).smallEtaleTopology (Type v)) :
    Set.BijOn (F.obj.map (etaleSpecMap (Algebra.ofId L E)).op)
      Set.univ
      {s | ∀ q : E ≃ₐ[L] E, F.obj.map (etaleSpecMap q).op s = s} := by
  let f := etaleSpecMap (Algebra.ofId L E)
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ f) ∈
      (Spec (.of L)).smallEtaleTopology (etaleSpec L L) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), (default : Spec (.of E)), @Subsingleton.elim (Spec (.of L)) _ _ _⟩
  have hsheaf : Presieve.IsSheafFor F.obj (Presieve.singleton f) := by
    rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ _).mp F.property _ hcov
  have hinj := Presieve.isSeparatedFor_singleton.mp hsheaf.isSeparatedFor
  refine ⟨?_, fun _ _ _ _ h ↦ hinj h, ?_⟩
  · intro s _ q
    change F.obj.map (etaleSpecMap q).op (F.obj.map f.op s) = F.obj.map f.op s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    have hq : etaleSpecMap q ≫ f = f := by
      rw [etaleSpecMap_comp]
      congr 1
      ext
    rw [hq]
  · intro s hs
    obtain ⟨hπ, hW, p₁, p₂, σ, hp₁, hp₂, hσ, β, hβ₁, hβ₂⟩ :=
      (AlgebraicGeometry.finiteGaloisTensorDecomposition L E F).2
    have hσ' (q : E ≃ₐ[L] E) : σ q = etaleSpecMap q := by
      apply MorphismProperty.Over.Hom.ext
      exact hσ q
    have heq : F.obj.map p₁.op s = F.obj.map p₂.op s := by
      apply β.injective
      funext q
      rw [hβ₁, hβ₂, hσ']
      exact (hs q).symm
    have hcompat {Z : (Spec (.of L)).Etale} (g₁ g₂ : Z ⟶ etaleSpec L E)
        (hg : g₁ ≫ f = g₂ ≫ f) : F.obj.map g₁.op s = F.obj.map g₂.op s := by
      let π := Spec.map (CommRingCat.ofHom (algebraMap L E))
      have hw : g₁.left ≫ π = g₂.left ≫ π :=
        (MorphismProperty.Over.w g₁).trans (MorphismProperty.Over.w g₂).symm
      let h : Z ⟶ Scheme.Etale.mk (Limits.pullback.fst π π ≫ π) :=
        MorphismProperty.Over.homMk (Limits.pullback.lift g₁.left g₂.left hw) (by
          change Limits.pullback.lift _ _ _ ≫ (Limits.pullback.fst π π ≫ π) = Z.hom
          rw [← Category.assoc, Limits.pullback.lift_fst]
          exact MorphismProperty.Over.w g₁)
      have hh₁ : h ≫ p₁ = g₁ := by
        apply MorphismProperty.Over.Hom.ext
        change Limits.pullback.lift _ _ _ ≫ p₁.left = g₁.left
        rw [hp₁, Limits.pullback.lift_fst]
      have hh₂ : h ≫ p₂ = g₂ := by
        apply MorphismProperty.Over.Hom.ext
        change Limits.pullback.lift _ _ _ ≫ p₂.left = g₂.left
        rw [hp₂, Limits.pullback.lift_snd]
      rw [← hh₁, ← hh₂]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      exact congr_arg (F.obj.map h.op) heq
    obtain ⟨t, ht, _⟩ := Presieve.isSheafFor_singleton.mp hsheaf s hcompat
    exact ⟨t, Set.mem_univ _, ht⟩

end AlgebraicGeometry.Scheme
