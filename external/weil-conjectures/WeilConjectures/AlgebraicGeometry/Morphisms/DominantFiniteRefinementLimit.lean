/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.PointedSectionStageDescent

/-!
# The limit of a dominant finite refinement

## References

* Stacks Project, Tag 0EZJ, normal-stage limit claim
* Tag 01ZM for morphism descent
* Stacks Project, Tag 0EZJ, the claim that the normal replacement diagram still has limit S
* Tag 01ZM for finite-presentation morphism descent
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A finite refinement with integral stages and dominant projections has the same
limit as the supplied Noetherian approximation. No normality of the stages or of S
is needed for this comparison, and no affine-transition hypothesis on X is needed. -/
theorem isLimit_of_dominant_finite_refinement {S : Scheme.{u}}
    (N : S.NoetherianApproximation)
    (X : N.I ⥤ Scheme.{u}) (α : (Functor.const N.I).obj S ⟶ X) (p : X ⟶ N.D)
    (hfac : α ≫ p = N.π)
    (hp : ∀ i, IsFinite (p.app i))
    (hX : ∀ i, IsIntegral (X.obj i))
    (hα : ∀ i, IsDominant (α.app i)) :
    Nonempty (IsLimit (Cone.mk S α)) := by
  have hfacapp (i : N.I) : α.app i ≫ p.app i = N.π.app i :=
    congrArg (fun t ↦ t.app i) hfac
  refine ⟨{ lift := fun c ↦ N.isLimit.lift (Cone.mk c.pt (c.π ≫ p))
            fac := ?_
            uniq := ?_ }⟩
  · intro c i
    have := hp i
    obtain ⟨j, f, a, hαj, hap⟩ := exists_map_at_refinement_of_affine_limit N.D
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      N.π N.isLimit i (p.app i) (α.app i) (hfacapp i)
    have := hX j
    have := hα j
    have hmap : p.app j ≫ a = X.map f := by
      apply ext_of_isDominant_of_isSeparated (p.app i) ?_ (α.app j)
      · rw [← Category.assoc, hfacapp j, hαj]
        simpa using α.naturality f
      · rw [Category.assoc, hap, p.naturality f]
    calc
      N.isLimit.lift (Cone.mk c.pt (c.π ≫ p)) ≫ α.app i =
          N.isLimit.lift (Cone.mk c.pt (c.π ≫ p)) ≫ N.π.app j ≫ a := by rw [hαj]
      _ = c.π.app j ≫ p.app j ≫ a := by
        rw [← Category.assoc, N.isLimit.fac]
        rfl
      _ = c.π.app j ≫ X.map f := by rw [hmap]
      _ = c.π.app i := c.w f
  · intro c m hm
    apply N.isLimit.hom_ext
    intro i
    calc
      m ≫ N.π.app i = m ≫ α.app i ≫ p.app i := by rw [hfacapp i]
      _ = c.π.app i ≫ p.app i := by rw [← Category.assoc, hm i]
      _ = N.isLimit.lift (Cone.mk c.pt (c.π ≫ p)) ≫ N.π.app i :=
        (N.isLimit.fac (Cone.mk c.pt (c.π ≫ p)) i).symm

end AlgebraicGeometry.Scheme
