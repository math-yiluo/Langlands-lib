/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectLifts
import WeilConjectures.FieldTheory.BrauerScalarDefectCocycle

/-!
# Existence of the scalar-defect class

Source: Stacks Project, Lemma 03R6 and the construction preceding Theorem 03R7.
(blueprint: lem-sc-brauer-scalar-defect-exists).
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A splitting admits locally constant matrix lifts and an actual scalar-defect cycle.

Proof: the given splitting is determined by finitely many matrix coefficients, all
algebraic and separable over K. Enlarge their field to a finite Galois extension.
Transport the semilinear Galois action across
`e`. Skolem--Noether expresses each transported automorphism as conjugation by an
invertible matrix. Choose these lifts on the finite Galois group and inflate them to
the absolute Galois group; the resulting function `b` is locally constant. Composition
of the transported actions implies that `b g * g(b h) * (b (g * h))⁻¹` is central,
hence a unique scalar unit. Associativity is precisely the multiplicative two-cocycle
identity. Change variables to obtain the invariant homogeneous cocycle
`f(g₀,g₁,g₂) = g₀(c(g₀⁻¹*g₁,g₁⁻¹*g₂))`, written additively in the units.
All its values and matrix entries lie in a finite extension, so it is jointly
continuous into the discrete coefficient group. The compact-open exponential law for
the compact Hausdorff Galois group curries it to Mathlib's iterated continuous cochains.
The cocycle identity puts it in the cycles object, producing `z`. The construction
of the scalar defect gives the claimed identity with its evaluation at `(1,g,g*h)`.

Source: Stacks Project, Lemma 03R6 and the scalar-defect construction immediately before
Theorem 03R7, with homogeneous coordinates as in Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-exists). -/
theorem exists_brauerScalarDefect_lifts (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K)) :
    ∃ b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      IsLocallyConstant b ∧
      ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
        (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
          (e (1 ⊗ₜ[K] a)).map g =
            ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
        (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
          Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
            b (g * h)) := by
  obtain ⟨b, hb, hdesc⟩ := exists_locallyConstant_brauer_lift K A n hn e
  obtain ⟨z, hdefect⟩ := exists_brauerScalarDefect_cocycle K A n hn e b hb hdesc
  exact ⟨b, hb, z, hdesc, hdefect⟩

end Field
