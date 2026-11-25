/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryDegreeIso

/-!
# Ordinary base tensor associativity

Source: Stacks Project, Tags 06Y6 and 08IB
(blueprint: lem-pc-base-tensor-ordinary-iso).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Stacks Project, Tag 08IB (affine tensor identification), and Tag 06Y6
(blueprint: lem-pc-base-tensor-ordinary-iso).

Proof: in each degree the forward map sends b tensor q to (1 tensor b) tensor q.
Its inverse sends (a tensor b) tensor q to b tensor (a q). The balancing relations
make both maps well defined and B-linear; the two composites are identity on pure
tensors, hence everywhere by tensor induction. These maps commute with the
A-linear differential of Q, so they give an isomorphism of complexes.
No flatness, localization, boundedness, or Tor-independence is used. -/
theorem exists_baseTensorOrdinaryIso
    (Q : CochainComplex (ModuleCat.{max uR uA uB v} A) ℤ)
    [(extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).Additive]
    [(extendScalars.{_, _, max uR uA uB v}
      (algebraMap A (A ⊗[R] B))).Additive] :
    ∃ (ordinaryIso :
      ((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
      (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q) ≅
    ((restrictScalars.{max uR uA uB v}
      Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj
      (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R]
      B))).mapHomologicalComplex (.up ℤ)).obj Q)),
      ∀ (i : ℤ) (b : B) (q : Q.X i),
    ordinaryIso.hom.f i (b ⊗ₜ[R,algebraMap R B] q) =
      (Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q) := by
  classical
  choose f hf using fun i => exists_baseTensorOrdinaryDegreeIso R A B (Q.X i)
  refine ⟨HomologicalComplex.Hom.isoOfComponents f ?_, ?_⟩
  · intro i j hij
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b q =>
      change B at b
      change Q.X i at q
      change
        (restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
          ((extendScalars (algebraMap A (A ⊗[R] B))).map (Q.d i j))
            ((f i).hom (b ⊗ₜ[R,algebraMap R B] q)) =
        (f j).hom (((extendScalars (algebraMap R B)).map
          ((restrictScalars (algebraMap R A)).map (Q.d i j)))
            (b ⊗ₜ[R,algebraMap R B] q))
      rw [hf i]
      change Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)]
        ((Q.d i j) q) =
        (f j).hom (b ⊗ₜ[R,algebraMap R B] ((Q.d i j) q))
      exact (hf j b ((Q.d i j) q)).symm
    | add x y hx hy => simp only [comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  · intro i b q
    exact hf i b q

end ModuleCat
