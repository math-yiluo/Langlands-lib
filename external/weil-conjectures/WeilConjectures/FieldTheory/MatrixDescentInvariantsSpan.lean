/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.MatrixDescentInvariants
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.Span.Basic

import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Invariant matrices span after extension of scalars

Source: Stacks Project, Tag 03R6, construction preceding Theorem 03R7.
(blueprint: lem-sc-matrix-descent-invariants-span).
-/

@[expose] public section

universe u

namespace Field

/-- Local constancy factors the matrix lifts through a finite Galois restriction map.
The existing open-normal-stabilizer theorem supplies a right stabilizer. The normal Krull
neighbourhood basis supplies a finite normal subfield with fixing subgroup inside it;
separability is inherited from the separable closure. Equal restrictions differ by an
element of this fixing subgroup, so their b-values coincide. -/
private theorem finite_factorization (K : Type u) [Field K] (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b) :
    ∃ L : FiniteGaloisIntermediateField K (SeparableClosure K),
      ∀ g h, AlgEquiv.restrictNormalHom L g = AlgEquiv.restrictNormalHom L h →
        b g = b h := by
  classical
  let S := SeparableClosure K
  let G := S ≃ₐ[K] S
  let B := Matrix.GeneralLinearGroup (Fin n) S
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
    (ProfiniteGrp.of G) B b ((IsLocallyConstant.iff_continuous b).mp hb)
  have hnhds : (U : Set G) ∈ nhds 1 := U.toOpenSubgroup.isOpen.mem_nhds U.one_mem
  obtain ⟨E, hfin, hnormal, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K S (U : Set G)).mp hnhds
  have := hfin
  have := hnormal
  have : Algebra.IsSeparable K E := inferInstance
  have : IsGalois K E := ⟨⟩
  let L : FiniteGaloisIntermediateField K S := ⟨E⟩
  refine ⟨L, ?_⟩
  intro g h hgh
  have hker : g⁻¹ * h ∈ (AlgEquiv.restrictNormalHom E).ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    change (AlgEquiv.restrictNormalHom L g)⁻¹ * AlgEquiv.restrictNormalHom L h = 1
    rw [hgh, inv_mul_cancel]
  have hfix : g⁻¹ * h ∈ E.fixingSubgroup := by
    rwa [E.restrictNormalHom_ker] at hker
  simpa using (hU g (g⁻¹ * h) (hE hfix)).symm

/-- The separable-closure span of twisted invariant matrices is the full matrix space.

Proof: local constancy on the compact absolute Galois group gives a finite image
and an open normal subgroup on whose cosets b is constant. Shrink this subgroup
so it fixes the entries of every b-value and its inverse. Its fixed field L is
finite Galois over K. The identity and composition hypotheses make the twisted
maps a semilinear action, trivial on the subgroup when restricted to Mat_n(L),
hence an action of Gal(L/K). For a in L and a matrix v over L, the sum of
sigma(a) T_sigma(v) over this finite group is invariant, by reindexing the sum.
If the L-span of these invariant sums were proper, choose a nonzero linear
functional annihilating it. For each v, independence of the distinct field
embeddings applied to the resulting identity in a forces every coefficient
lambda(T_sigma(v)) to vanish, including lambda(v). This contradicts the choice
of lambda. Thus invariant matrices span Mat_n(L). The matrix units show that
Mat_n(L) spans Mat_n(SeparableClosure K), giving the asserted span equality.
For n=0 the matrix space is zero and the argument uses the empty basis.
No averaging by division by the group order is involved.

Source: Stacks Project, Tag 03R6, finite descent argument expanded in steps 1--3
of lem-sc-matrix-descent-scalar-map-bijective.
(blueprint: lem-sc-matrix-descent-invariants-span). -/
theorem matrixDescentInvariants_span (K : Type u) [Field K] (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M)
    (hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val) :
    Submodule.span (SeparableClosure K)
      (Set.range fun a : matrixDescentInvariants K n b ↦
        (a : Matrix (Fin n) (Fin n) (SeparableClosure K))) = ⊤ := by
  classical
  let S := SeparableClosure K
  let G := S ≃ₐ[K] S
  let V := Matrix (Fin n) (Fin n) S
  -- Only factor b through a finite quotient; its entries need not be descended.
  obtain ⟨L, hL⟩ := finite_factorization K n b hb
  let q : G →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let s : (L ≃ₐ[K] L) → G := fun σ ↦ σ.liftNormal S
  have hs (σ : L ≃ₐ[K] L) : q (s σ) = σ := σ.restrict_liftNormal S
  let T : G → V →+ V := fun g ↦
    { toFun := fun M ↦ (b g).val * M.map g * ((b g)⁻¹).val
      map_zero' := by simp
      map_add' := by
        intro M N
        change (b g).val * g.toAlgHom.mapMatrix (M + N) * ((b g)⁻¹).val = _
        rw [map_add, mul_add, add_mul]
        rfl }
  have T_smul (g : G) (a : S) (M : V) : T g (a • M) = g a • T g M := by
    change (b g).val * (a • M).map g * ((b g)⁻¹).val = _
    have hmap : (a • M).map g = g a • M.map g := by
      apply Matrix.ext
      intro i j
      exact g.map_mul a (M i j)
    rw [hmap, mul_smul_comm, smul_mul_assoc]
    rfl
  have T_mul (g h : G) (M : V) : T g (T h M) = T (g * h) M := hm g h M
  have unit_fixed (g : G) (i j : Fin n) :
      (Matrix.single i j (1 : S)).map g = Matrix.single i j 1 := by
    simp [Matrix.map_single]
  have T_unit (g h : G) (i j : Fin n) (hgh : q g = q h) :
      T g (Matrix.single i j 1) = T h (Matrix.single i j 1) := by
    change (b g).val * _ * ((b g)⁻¹).val = (b h).val * _ * ((b h)⁻¹).val
    rw [unit_fixed, unit_fixed, hL g h hgh]
  have T_one (M : V) : T 1 M = M := by
    change (b 1).val * M.map (1 : G) * ((b 1)⁻¹).val = M
    have hmap : M.map (1 : G) = M := rfl
    rw [hmap]
    exact h1 M
  let : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  -- Weighted orbit sums of matrix units are invariant, in every characteristic.
  let avg (a : L) (i j : Fin n) : V :=
    ∑ σ : L ≃ₐ[K] L, (σ a : S) • T (s σ) (Matrix.single i j 1)
  have havg (a : L) (i j : Fin n) : avg a i j ∈ matrixDescentInvariants K n b := by
    intro g
    change T g (avg a i j) = avg a i j
    change T g (∑ σ : L ≃ₐ[K] L, (σ a : S) • T (s σ) (Matrix.single i j 1)) = _
    rw [map_sum]
    calc
      _ = ∑ σ : L ≃ₐ[K] L,
          ((q g * σ) a : S) • T (s (q g * σ)) (Matrix.single i j 1) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [T_smul, T_mul]
        have hscalar : g (σ a : S) = ((q g * σ) a : S) :=
          (AlgEquiv.restrictNormal_commutes g L (σ a)).symm
        rw [hscalar, T_unit (g * s σ) (s (q g * σ)) i j (by simp [q, hs])]
      _ = avg a i j := by
        exact Fintype.sum_equiv (Equiv.mulLeft (q g)) _ _ (fun _ ↦ rfl)
  let W : Submodule S V := Submodule.span S
    (Set.range fun a : matrixDescentInvariants K n b ↦ (a : V))
  -- An annihilating functional would contradict independence of field embeddings.
  have hunit (i j : Fin n) : Matrix.single i j (1 : S) ∈ W := by
    by_contra hn
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hn
    have hid : LinearIndependent S (fun σ : L ≃ₐ[K] L ↦ fun a : L ↦ (σ a : S)) := by
      let emb : (L ≃ₐ[K] L) → (L →* S) :=
        fun σ ↦ L.toIntermediateField.val.toMonoidHom.comp σ.toMonoidHom
      have hemb : Function.Injective emb := by
        intro σ τ hστ
        apply AlgEquiv.ext
        intro a
        apply Subtype.val_injective
        exact DFunLike.congr_fun hστ a
      exact (linearIndependent_monoidHom L S).comp emb hemb
    have hzero : ∑ σ : L ≃ₐ[K] L,
        f (T (s σ) (Matrix.single i j 1)) • (fun a : L ↦ (σ a : S)) = 0 := by
      funext a
      have havgW : avg a i j ∈ W :=
        Submodule.subset_span ⟨⟨avg a i j, havg a i j⟩, rfl⟩
      have hfavg : f (avg a i j) = 0 := hker havgW
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      calc
        _ = ∑ σ : L ≃ₐ[K] L, (σ a : S) * f (T (s σ) (Matrix.single i j 1)) := by
          apply Finset.sum_congr rfl
          intro σ _
          exact mul_comm _ _
        _ = 0 := by
          simpa only [avg, map_sum, map_smul, smul_eq_mul] using hfavg
    have hcoef := Fintype.linearIndependent_iff.mp hid
      (fun σ ↦ f (T (s σ) (Matrix.single i j 1))) hzero 1
    rw [T_unit (s 1) 1 i j (by rw [hs, map_one]), T_one] at hcoef
    exact hf hcoef
  apply top_unique
  intro M _
  change M ∈ W
  rw [Matrix.matrix_eq_sum_single M]
  apply W.sum_mem
  intro i _
  apply W.sum_mem
  intro j _
  have hsingle : Matrix.single i j (M i j) = M i j • Matrix.single i j 1 := by
    simp [Matrix.smul_single, smul_eq_mul]
  rw [hsingle]
  exact W.smul_mem (M i j) (hunit i j)

end Field
