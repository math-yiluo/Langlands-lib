/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentDataExistence
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Full faithfulness of finite etale descent

Source: Stacks Project, Descent, Tag 02W0, via effective epimorphisms
(blueprint: lem-galois-descent-fully-faithful).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Canonical base change is fully faithful along an etale surjection.
Source: Stacks Project, Descent, Tag 02W0; Step 3 of `lem-galois-descent`
(blueprint: lem-galois-descent-fully-faithful).

Proof: the first projection of every pullback is an etale surjection, hence
an effective epimorphism. A compatible morphism followed by the first
projection has equal values on any pair of points with the same image:
transport takes one point to the other by pullback uniqueness. The effective
epimorphism descends this map uniquely. Its factorization shows it is a map
over the base. Pullback uniqueness identifies its base change with the given
map, and epimorphism cancellation proves faithfulness. -/
theorem finiteEtaleDescent_fullyFaithful {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g]
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left)
    (h : FiniteEtaleDescentCompatible F q) : Nonempty F.FullyFaithful := by
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective F).mpr
  intro P Q
  obtain ⟨_, hp, htP⟩ := h.1 P
  obtain ⟨_, hq, htQ⟩ := h.1 Q
  have : Flat (q P) := MorphismProperty.of_isPullback hp.flip inferInstance
  have : Surjective (q P) := MorphismProperty.of_isPullback hp.flip inferInstance
  have : LocallyOfFinitePresentation (q P) :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  refine ⟨?_, ?_⟩
  · intro f k e
    apply Scheme.FiniteEtale.hom_ext
    apply (cancel_epi (q P)).1
    rw [← h.2 P Q f, ← h.2 P Q k, e]
  · intro b
    let ψ := b.hom.hom
    have hc : ∀ {T : Scheme.{v}} (a c : T ⟶ (F.obj P).obj.V.left),
        a ≫ q P = c ≫ q P →
        a ≫ (ψ.left ≫ q Q) = c ≫ (ψ.left ≫ q Q) := by
      intro T a c hac
      have hf : (a ≫ (F.obj P).obj.V.hom) ≫ g =
          (c ≫ (F.obj P).obj.V.hom) ≫ g := by
        simpa only [Category.assoc, ← hp.w] using congrArg (· ≫ P.obj.hom) hac
      let aa : Over.mk (a ≫ (F.obj P).obj.V.hom) ⟶ (F.obj P).obj.V := Over.homMk a
      let cc : Over.mk (c ≫ (F.obj P).obj.V.hom) ⟶ (F.obj P).obj.V := Over.homMk c
      have ht : (F.obj P).obj.datum.transport _ _ hf aa = cc := by
        apply Over.OverMorphism.ext
        apply hp.hom_ext
        · exact (htP _ _ hf aa).trans hac
        · simp [cc]
      have hw := htQ _ _ hf (aa ≫ ψ)
      rw [b.hom.commutes, ht] at hw
      exact hw.symm
    let ψ₀ := EffectiveEpi.desc (q P) (ψ.left ≫ q Q) hc
    have hfac : q P ≫ ψ₀ = ψ.left ≫ q Q := EffectiveEpi.fac _ _ _
    have hover : ψ₀ ≫ Q.obj.hom = P.obj.hom := by
      apply (cancel_epi (q P)).1
      rw [← Category.assoc, hfac, Category.assoc, hq.w, ← Category.assoc,
        Over.w ψ, hp.w]
    let f : P ⟶ Q := ObjectProperty.homMk (MorphismProperty.Over.homMk ψ₀ hover)
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.DescentDataCategory.Hom.ext
    apply Over.OverMorphism.ext
    apply hq.hom_ext
    · exact (h.2 P Q f).trans hfac
    · exact (Over.w (F.map f).hom.hom).trans (Over.w ψ).symm

end AlgebraicGeometry
