/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Invariant vectors span for locally constant Galois matrix cocycles. -/
@[expose] public section
universe u
namespace Field
/-- The invariant vectors span over the separable closure.

Proof: an open normal right stabilizer of b and the normal Krull neighbourhood basis
provide a finite Galois intermediate field L such that b depends only on restriction to L.
Write q for restriction and choose lifts s of its automorphisms. Let T_g(v)=b(g)g(v).
The cocycle law gives T_g T_h=T_(gh) and b(1)=1. On each standard vector e_i, T_g(e_i)
depends only on q(g). For a in L form A(a,i)=sum_sigma sigma(a) T_(s sigma)(e_i).
Semilinearity, the cocycle law and reindexing by left multiplication by q(g) show that
A(a,i) is fixed by every T_g. Let W be the S-span of fixed vectors, where S is the
separable closure. If e_i is not in W, take an S-linear functional f vanishing on W but
not on e_i. The equality f(A(a,i))=0 for every a in L is a linear relation among the
distinct embeddings of L into S. Their independence forces each coefficient to vanish.
At the identity this coefficient is f(e_i), a contradiction. Thus all standard vectors
belong to W and W is top. The argument includes n=0 and uses no division by group order.
The finite-factorization and weighted-averaging proof is adapted from
Field.matrixDescentInvariants_span in WeilConjectures.FieldTheory.MatrixDescentInvariantsSpan;
the vector action here is left multiplication rather than matrix conjugation.
Source: Stacks Project, Tag 03R7, injectivity via invariant-basis descent.
(blueprint: lem-sc-galois-invariant-vectors-span) -/
theorem galois_invariant_vectors_span (K : Type u) [Field K] (n : ℕ)
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    Submodule.span (SeparableClosure K)
      {v : Fin n → SeparableClosure K | ∀ g, (b g).val.mulVec (g ∘ v) = v} = ⊤ := by
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
  have hL : ∀ g h : G,
      AlgEquiv.restrictNormalHom L g = AlgEquiv.restrictNormalHom L h → b g = b h := by
    intro g h hgh
    have hker : g⁻¹ * h ∈ (AlgEquiv.restrictNormalHom E).ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      change (AlgEquiv.restrictNormalHom L g)⁻¹ * AlgEquiv.restrictNormalHom L h = 1
      rw [hgh, inv_mul_cancel]
    have hfix : g⁻¹ * h ∈ E.fixingSubgroup := by
      rwa [E.restrictNormalHom_ker] at hker
    simpa using (hU g (g⁻¹ * h) (hE hfix)).symm
  let V := Fin n → S
  let q : G →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let s : (L ≃ₐ[K] L) → G := fun σ ↦ σ.liftNormal S
  have hs (σ : L ≃ₐ[K] L) : q (s σ) = σ := σ.restrict_liftNormal S
  let T : G → V →+ V := fun g ↦
    { toFun := fun v ↦ (b g).val.mulVec (g ∘ v)
      map_zero' := by
        change (b g).val.mulVec (g ∘ (0 : V)) = 0
        have hmap : g ∘ (0 : V) = (0 : V) := by
          funext i
          exact g.map_zero
        rw [hmap]
        exact Matrix.mulVec_zero _
      map_add' := by
        intro v w
        have hmap : g ∘ (v + w) = g ∘ v + g ∘ w := by
          funext i
          exact g.map_add _ _
        rw [hmap, Matrix.mulVec_add] }
  have T_smul (g : G) (a : S) (v : V) : T g (a • v) = g a • T g v := by
    change (b g).val.mulVec (g ∘ (a • v)) = _
    have hmap : g ∘ (a • v) = g a • (g ∘ v) := by
      funext i
      exact g.map_mul _ _
    rw [hmap, Matrix.mulVec_smul]
    rfl
  have T_mul (g h : G) (v : V) : T g (T h v) = T (g * h) v := by
    change (b g).val.mulVec (g ∘ ((b h).val.mulVec (h ∘ v))) = _
    have hmap : g ∘ ((b h).val.mulVec (h ∘ v)) =
        ((b h).val.map g).mulVec ((g * h) ∘ v) := by
      funext i
      exact RingHom.map_mulVec g.toRingHom (b h).val (h ∘ v) i
    rw [hmap, Matrix.mulVec_mulVec]
    have hc := congrArg Units.val (hcoc g h)
    change (b g).val * (b h).val.map g = (b (g * h)).val at hc
    rw [hc]
    rfl
  have unit_fixed (g : G) (i : Fin n) :
      g ∘ Pi.single i (1 : S) = Pi.single i 1 := by
    funext j
    by_cases h : j = i <;> simp [h]
  have T_unit (g h : G) (i : Fin n) (hgh : q g = q h) :
      T g (Pi.single i 1) = T h (Pi.single i 1) := by
    change (b g).val.mulVec _ = (b h).val.mulVec _
    rw [unit_fixed, unit_fixed, hL g h hgh]
  have T_one (v : V) : T 1 v = v := by
    have hb1 : b 1 = 1 := by
      have h := hcoc 1 1
      change b 1 * b 1 = b 1 at h
      exact mul_left_cancel (h.trans (mul_one (b 1)).symm)
    change (b 1).val.mulVec ((1 : G) ∘ v) = v
    rw [hb1]
    exact Matrix.one_mulVec v
  let : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  let avg (a : L) (i : Fin n) : V :=
    ∑ σ : L ≃ₐ[K] L, (σ a : S) • T (s σ) (Pi.single i 1)
  have havg (a : L) (i : Fin n) : ∀ g, (b g).val.mulVec (g ∘ avg a i) = avg a i := by
    intro g
    change T g (avg a i) = avg a i
    change T g (∑ σ : L ≃ₐ[K] L, (σ a : S) • T (s σ) (Pi.single i 1)) = _
    rw [map_sum]
    calc
      _ = ∑ σ : L ≃ₐ[K] L,
          ((q g * σ) a : S) • T (s (q g * σ)) (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [T_smul, T_mul]
        have hscalar : g (σ a : S) = ((q g * σ) a : S) :=
          (AlgEquiv.restrictNormal_commutes g L (σ a)).symm
        rw [hscalar, T_unit (g * s σ) (s (q g * σ)) i (by simp [q, hs])]
      _ = avg a i := by
        exact Fintype.sum_equiv (Equiv.mulLeft (q g)) _ _ (fun _ ↦ rfl)
  let W : Submodule S V := Submodule.span S
    {v : V | ∀ g, (b g).val.mulVec (g ∘ v) = v}
  -- An annihilating functional would contradict independence of field embeddings.
  have hunit (i : Fin n) : Pi.single i (1 : S) ∈ W := by
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
        f (T (s σ) (Pi.single i 1)) • (fun a : L ↦ (σ a : S)) = 0 := by
      funext a
      have havgW : avg a i ∈ W :=
        Submodule.subset_span (havg a i)
      have hfavg : f (avg a i) = 0 := hker havgW
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      calc
        _ = ∑ σ : L ≃ₐ[K] L, (σ a : S) * f (T (s σ) (Pi.single i 1)) := by
          apply Finset.sum_congr rfl
          intro σ _
          exact mul_comm _ _
        _ = 0 := by
          simpa only [avg, map_sum, map_smul, smul_eq_mul] using hfavg
    have hcoef := Fintype.linearIndependent_iff.mp hid
      (fun σ ↦ f (T (s σ) (Pi.single i 1))) hzero 1
    rw [T_unit (s 1) 1 i (by rw [hs, map_one]), T_one] at hcoef
    exact hf hcoef
  apply top_unique
  intro v _
  change v ∈ W
  have hv : ∑ i, Pi.single i (v i) = v := by
    ext j
    simp
  rw [← hv]
  apply W.sum_mem
  intro i _
  have hsingle : Pi.single i (v i) = v i • (Pi.single i (1 : S) : V) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [hsingle]
  exact W.smul_mem (v i) (hunit i)

end Field
