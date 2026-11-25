/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal

/-!
# Finite normal replacements of the stages of a Noetherian approximation

## References

* Stacks Project, Tag 0EZJ, normal approximation paragraph
* Stacks Project, Tag 0EZJ, the paragraph constructing the normal integral stages
* Tags 035E, 035N and 035L, and finiteness of normalization over the integers
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The scheme-theoretic images of the projections, normalized in their own function
fields, form a compatible finite normal replacement diagram. This assertion constructs
only a diagram and a cone; it does not assert that the cone is limiting. -/
theorem exists_normal_finite_stage_diagram {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (N : S.NoetherianApproximation) :
    ∃ (X : N.I ⥤ Scheme.{u}) (α : (Functor.const N.I).obj S ⟶ X) (p : X ⟶ N.D),
      α ≫ p = N.π ∧
      (∀ i, IsFinite (p.app i)) ∧
      (∀ i, IsDominant (α.app i)) ∧
      (∀ i, IsIntegral (X.obj i) ∧
        ∀ x : X.obj i, IsIntegrallyClosed ((X.obj i).presheaf.stalk x)) := by
  classical
  choose X α p hcomp hfin hdom hint hnormal hlift using
    exists_normal_finite_stage_universal hS N
  have hex {i j : N.I} (f : i ⟶ j) :
      ∃! g : X i ⟶ X j, α i ≫ g = α j ∧ g ≫ p j = p i ≫ N.D.map f := by
    apply hlift j (X i) (hint i) (hnormal i) (α i) (hdom i) (p i ≫ N.D.map f)
    rw [← Category.assoc, hcomp i]
    simpa using (N.π.naturality f).symm
  let m {i j : N.I} (f : i ⟶ j) : X i ⟶ X j := (hex f).choose
  have hm {i j : N.I} (f : i ⟶ j) :
      α i ≫ m f = α j ∧ m f ≫ p j = p i ≫ N.D.map f := (hex f).choose_spec.1
  have hu {i j : N.I} (f : i ⟶ j) (g : X i ⟶ X j)
      (hg : α i ≫ g = α j ∧ g ≫ p j = p i ≫ N.D.map f) : g = m f :=
    (hex f).choose_spec.2 g hg
  let F : N.I ⥤ Scheme.{u} :=
    { obj := X
      map := m
      map_id := fun i ↦ (hu (𝟙 i) (𝟙 (X i)) (by simp)).symm
      map_comp := fun f g ↦ (hu (f ≫ g) (m f ≫ m g) (by
        constructor
        · rw [← Category.assoc, (hm f).1, (hm g).1]
        · rw [Category.assoc, (hm g).2, ← Category.assoc, (hm f).2,
            Category.assoc, N.D.map_comp])).symm }
  let a : (Functor.const N.I).obj S ⟶ F :=
    { app := α
      naturality := fun i j f ↦ by simpa using (hm f).1.symm }
  let q : F ⟶ N.D :=
    { app := p
      naturality := fun i j f ↦ (hm f).2 }
  refine ⟨F, a, q, ?_, hfin, hdom, fun i ↦ ⟨hint i, hnormal i⟩⟩
  ext i
  exact hcomp i

end AlgebraicGeometry.Scheme
