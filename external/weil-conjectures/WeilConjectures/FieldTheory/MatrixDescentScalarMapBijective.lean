/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.MatrixDescentInvariants
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.MatrixDescentInvariantsSpan
import WeilConjectures.FieldTheory.MatrixDescentInvariantsLinearIndependent
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar extension of twisted Galois invariants

Source: Stacks Project, Lemma 03R6, preceding Theorem 03R7.
(blueprint: lem-sc-matrix-descent-scalar-map-bijective).
-/

@[expose] public section

universe u

namespace Field

/-- Scalar extension of the explicitly constructed invariant algebra is bijective.

Proof: compactness of the absolute Galois group and local constancy give finitely
many values of b and an open normal subgroup N on whose cosets b is constant.
Shrink N to fix every entry of these values. Its fixed field L is finite Galois
over K. The identity hypothesis says b(1) commutes with every matrix. Thus for
g in N, the twisted action is entrywise g-action, so the invariant matrices have
entries in L. The action on Mat_n(L) factors through Gamma = Gal(L/K).
For v in Mat_n(L) and a in L, the sum of g(a) T_g(v) over Gamma is invariant:
applying T_h reindexes by g ↦ hg. If an L-linear functional kills all these sums,
linear independence of distinct field automorphisms implies it kills T_g(v) for
all g and v, hence kills v. A proper span admits a nonzero annihilating functional;
therefore invariant vectors span Mat_n(L). Select an L-basis of invariant vectors.
The coefficients of an invariant linear combination are fixed by Gamma and
therefore in K. This basis is also a K-basis of the invariant algebra. Hence the
multiplication map L tensor_K A → Mat_n(L) is bijective. Extending scalars to Ksep
and using the same basis proves bijectivity of the displayed explicit map.
No division by the order of Gamma is used, and scalar unnormalized lifts are allowed.

Source: Stacks Project, construction preceding Theorem 03R7; finite Galois descent
expanded in steps 1 and 2 of lem-sc-projective-matrix-descent here.
(blueprint: lem-sc-matrix-descent-scalar-map-bijective). -/
theorem matrixDescentScalarMap_bijective (K : Type u) [Field K]
    (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M)
    (hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val) :
    Function.Bijective (matrixDescentScalarMap K n b) := by
  classical
  let A := matrixDescentInvariants K n b
  let c := Module.Free.chooseBasis K A
  let f := (matrixDescentScalarMap K n b).toLinearMap
  have hf (i) : f (c.baseChange (SeparableClosure K) i) =
      (c i : Matrix (Fin n) (Fin n) (SeparableClosure K)) := by
    rw [Module.Basis.baseChange_apply]
    exact matrixDescentScalarMap_one_tmul K n b (c i)
  have hli : LinearIndependent (SeparableClosure K)
      (f ∘ (c.baseChange (SeparableClosure K))) := by
    simpa only [Function.comp_def, hf] using
      matrixDescentInvariants_linearIndependent K n b c c.linearIndependent
  have hspan : Submodule.span (SeparableClosure K)
      (Set.range (f ∘ (c.baseChange (SeparableClosure K)))) = ⊤ := by
    have hc : Submodule.span K
        (Set.range fun i ↦ (c i : Matrix (Fin n) (Fin n) (SeparableClosure K))) =
        A.toSubmodule := by
      calc
        _ = (Submodule.span K (Set.range c)).map A.toSubmodule.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        _ = A.toSubmodule := by rw [c.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hrange : Submodule.span (SeparableClosure K)
        (Set.range fun i ↦ (c i : Matrix (Fin n) (Fin n) (SeparableClosure K))) =
        Submodule.span (SeparableClosure K)
          (Set.range fun a : A ↦ (a : Matrix (Fin n) (Fin n) (SeparableClosure K))) := by
      apply le_antisymm
      · apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨c i, rfl⟩
      · apply Submodule.span_le.mpr
        rintro _ ⟨a, rfl⟩
        have ha : (a : Matrix (Fin n) (Fin n) (SeparableClosure K)) ∈
            Submodule.span K
              (Set.range fun i ↦ (c i : Matrix (Fin n) (Fin n) (SeparableClosure K))) := by
          rw [hc]
          exact a.property
        exact Submodule.span_le_restrictScalars K (SeparableClosure K) _ ha
    simpa only [Function.comp_def, hf] using
      hrange.trans (matrixDescentInvariants_span K n b hb h1 hm)
  exact LinearMap.bijective_of_linearIndependent_of_span_eq_top
    (c.baseChange (SeparableClosure K)).span_eq hli hspan

end Field
