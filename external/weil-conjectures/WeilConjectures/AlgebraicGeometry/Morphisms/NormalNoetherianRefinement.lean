/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalFiniteStageDiagram
import WeilConjectures.AlgebraicGeometry.Morphisms.DominantFiniteRefinementLimit

/-!
# Normal refinement of an absolute Noetherian approximation

## References

* Stacks Project, Tag 0EZJ, normal approximation paragraph
* Stacks Project, Tag 0EZJ, first two approximation paragraphs
* Tags 01ZA, 035E, 035N and 035L for approximation and normalization
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- An ordinary Noetherian approximation of a normal integral scheme admits a normal
integral refinement with dominant projections. -/
theorem exists_normal_noetherian_refinement {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (N : S.NoetherianApproximation) :
    ∃ (I : Type u) (hcat : SmallCategory I),
      letI : SmallCategory I := hcat
      ∃ (hco : IsCofiltered I) (X : I ⥤ Scheme.{u})
        (α : (Functor.const I).obj S ⟶ X) (hα : IsLimit (Cone.mk S α))
        (hI : ∀ i, IsIntegral (X.obj i)),
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (X.map f)) ∧
        (∀ i, IsDominant (α.app i)) ∧
        (∀ i, IsNoetherian (X.obj i) ∧ QuasiSeparatedSpace (X.obj i) ∧
          ∀ x : X.obj i, IsIntegrallyClosed ((X.obj i).presheaf.stalk x)) := by
  obtain ⟨X, α, p, hfac, hp, hdom, hstage⟩ :=
    exists_normal_finite_stage_diagram hS N
  have hI : ∀ i, IsIntegral (X.obj i) := fun i ↦ (hstage i).1
  have haff : ∀ {i j : N.I} (f : i ⟶ j), IsAffineHom (X.map f) := by
    intro i j f
    have := hp i
    have := hp j
    have : IsAffineHom (X.map f ≫ p.app j) := by
      rw [p.naturality f]
      infer_instance
    exact IsAffineHom.of_comp (X.map f) (p.app j)
  obtain ⟨hlim⟩ :=
    isLimit_of_dominant_finite_refinement N X α p hfac hp hI hdom
  refine ⟨N.I, inferInstance, inferInstance, X, α, hlim, hI, haff, hdom, ?_⟩
  intro i
  have := hp i
  have : CompactSpace (X.obj i) := QuasiCompact.compactSpace_of_compactSpace (p.app i)
  have : IsLocallyNoetherian (X.obj i) :=
    LocallyOfFiniteType.isLocallyNoetherian (p.app i)
  have hnoeth : IsNoetherian (X.obj i) := ⟨⟩
  exact ⟨hnoeth, inferInstance, (hstage i).2⟩

end AlgebraicGeometry.Scheme
