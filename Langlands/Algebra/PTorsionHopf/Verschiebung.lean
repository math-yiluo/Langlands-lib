import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Langlands.GroupScheme.KostantRosenlicht.Points

/-! # Vanishing Verschiebung for reduced commutative bialgebras killed by `p` -/

noncomputable section

open Coalgebra WithConv

namespace Langlands.Algebra.PTorsionHopf

section Duality

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A functional on the dual space that kills every functional vanishing on a finite set is
evaluation at a vector. -/
theorem exists_eq_apply_of_finset (S : Finset V) (L : Module.Dual k V →ₗ[k] k)
    (hL : ∀ ξ : Module.Dual k V, (∀ s ∈ S, ξ s = 0) → L ξ = 0) :
    ∃ w : V, ∀ ξ : Module.Dual k V, L ξ = ξ w := by
  set W := Submodule.span k (S : Set V)
  obtain ⟨sec, hsec⟩ := W.subtype.dualMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (LinearMap.dualMap_surjective_of_injective W.injective_subtype))
  have hres : ∀ (φ : Module.Dual k W) (w : W), sec φ w = φ w := fun φ w =>
    LinearMap.congr_fun (LinearMap.congr_fun hsec φ) w
  refine ⟨((Module.evalEquiv k W).symm (L ∘ₗ sec) : W), fun ξ => ?_⟩
  have h0 : L (ξ - sec (W.subtype.dualMap ξ)) = 0 := by
    apply hL
    intro s hs
    rw [LinearMap.sub_apply, sub_eq_zero]
    have h := hres (W.subtype.dualMap ξ) ⟨s, Submodule.subset_span hs⟩
    rw [LinearMap.dualMap_apply] at h
    exact h.symm
  rw [map_sub, sub_eq_zero] at h0
  rw [h0]
  have h1 := Module.apply_evalEquiv_symm_apply (R := k) (M := W) (W.subtype.dualMap ξ)
    (L ∘ₗ sec)
  rw [LinearMap.dualMap_apply] at h1
  exact h1.symm

end Duality

section Finite

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A]

/-- The value of a convolution power at an element depends only on finitely many values of
the functional. -/
theorem exists_finset_convPow (m : ℕ) (a : A) :
    ∃ S : Finset A, ∀ ξ ξ' : WithConv (A →ₗ[k] k),
      (∀ s ∈ S, ξ s = ξ' s) → (ξ ^ m) a = (ξ' ^ m) a := by
  classical
  induction m generalizing a with
  | zero => exact ⟨∅, fun ξ ξ' _ => by rw [pow_zero, pow_zero]⟩
  | succ m ih =>
    choose S hS using ih
    let 𝓡 := ℛ k a
    refine ⟨𝓡.index.biUnion (fun i => S (𝓡.left i)) ∪ 𝓡.index.image 𝓡.right, ?_⟩
    intro ξ ξ' h
    rw [pow_succ, pow_succ, 𝓡.convMul_apply, 𝓡.convMul_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hS (𝓡.left i) ξ ξ' (fun s hs => h s (Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨i, hi, hs⟩))),
      h _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))]

end Finite

section Verschiebung

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A] [IsCocomm k A]
  (p : ℕ) [Fact p.Prime] [CharP k p]

omit [IsCocomm k A] in
theorem convOne_apply_one : (1 : WithConv (A →ₗ[k] k)) 1 = 1 := by
  rw [LinearMap.convOne_apply, Bialgebra.counit_one, Algebra.algebraMap_self, RingHom.id_apply]

instance : Nontrivial (WithConv (A →ₗ[k] k)) :=
  nontrivial_of_ne 1 0 fun h => by
    have := congrArg (fun ξ : WithConv (A →ₗ[k] k) => ξ 1) h
    simp only [convOne_apply_one] at this
    exact one_ne_zero (this.trans (by rfl))

omit [IsCocomm k A] [Fact p.Prime] in
theorem charP_dual : CharP (WithConv (A →ₗ[k] k)) p :=
  charP_of_injective_algebraMap (algebraMap k (WithConv (A →ₗ[k] k))).injective p

/-- The `p`-th power map on the convolution dual, evaluated at `a`, is additive. -/
theorem convPow_char_add (ξ η : WithConv (A →ₗ[k] k)) (a : A) :
    ((ξ + η) ^ p) a = (ξ ^ p) a + (η ^ p) a := by
  have := charP_dual (k := k) (A := A) p
  rw [add_pow_char]
  rfl

omit [IsCocomm k A] [Fact p.Prime] [CharP k p] in
/-- The `p`-th power map on the convolution dual is `p`-semilinear. -/
theorem convPow_char_smul (c : k) (ξ : WithConv (A →ₗ[k] k)) (a : A) :
    ((c • ξ) ^ p) a = c ^ p * (ξ ^ p) a := by
  rw [smul_pow]
  rfl

variable [PerfectRing k p]

/-- The `p`-th root of the `p`-th power map, as a linear functional on the dual. -/
def rootPowFunctional (a : A) : Module.Dual k A →ₗ[k] k where
  toFun ξ := (frobeniusEquiv k p).symm ((toConv ξ ^ p) a)
  map_add' ξ η := by
    rw [toConv_add, convPow_char_add, map_add]
  map_smul' c ξ := by
    rw [toConv_smul, convPow_char_smul, map_mul, RingHom.id_apply, smul_eq_mul]
    congr 1
    rw [← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

theorem frobeniusEquiv_symm_eq_iff {x y : k} : (frobeniusEquiv k p).symm x = y ↔ x = y ^ p := by
  rw [RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def]

variable [IsAlgClosed k] [Algebra.FiniteType k A] [IsReduced A]

/-- **Vanishing Verschiebung.** If every `k`-point of a reduced finitely generated commutative
and cocommutative bialgebra over an algebraically closed field of characteristic `p` is killed
by `p` in the convolution group, then `p`-th convolution powers of functionals are
`ξ ^ p = ξ(1) ^ p • ε`. -/
theorem convPow_char_apply (hA : ∀ φ : A →ₐ[k] k, toConv φ.toLinearMap ^ p = 1)
    (ξ : WithConv (A →ₗ[k] k)) (a : A) :
    (ξ ^ p) a = counit a * ξ 1 ^ p := by
  obtain ⟨S, hS⟩ := exists_finset_convPow (k := k) p a
  obtain ⟨w, hw⟩ := exists_eq_apply_of_finset S (rootPowFunctional p a) (fun ξ hξ => by
    change (frobeniusEquiv k p).symm _ = 0
    rw [hS (toConv ξ) 0 (fun s hs => by simp [hξ s hs]),
      zero_pow (Fact.out : p.Prime).ne_zero]
    simp)
  have hΨ : ∀ ξ : WithConv (A →ₗ[k] k), (ξ ^ p) a = ξ w ^ p := fun ξ => by
    have h := hw ξ.ofConv
    change (frobeniusEquiv k p).symm ((toConv ξ.ofConv ^ p) a) = _ at h
    rw [frobeniusEquiv_symm_eq_iff, toConv_ofConv] at h
    exact h
  set c := (frobeniusEquiv k p).symm (counit a) with hc
  have hpt : ∀ φ : A →ₐ[k] k, φ w = c := fun φ => by
    have h := hΨ (toConv φ.toLinearMap)
    rw [hA φ, LinearMap.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
    rw [hc, eq_comm, frobeniusEquiv_symm_eq_iff, h]
    rfl
  have hw' : w = algebraMap k A c := by
    rw [← sub_eq_zero]
    refine GroupScheme.KostantRosenlicht.eq_zero_of_forall_algHom (k := k) fun φ => ?_
    rw [map_sub, hpt φ, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [hΨ ξ, hw', Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_pow, hc,
    frobeniusEquiv_symm_pow_p]

/-- In particular every functional killing `1` has vanishing `p`-th convolution power. -/
theorem convPow_char_eq_zero (hA : ∀ φ : A →ₐ[k] k, toConv φ.toLinearMap ^ p = 1)
    {ξ : WithConv (A →ₗ[k] k)} (hξ : ξ 1 = 0) : ξ ^ p = 0 := by
  ext a
  rw [convPow_char_apply p hA, hξ, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero]
  rfl

end Verschiebung

end Langlands.Algebra.PTorsionHopf
