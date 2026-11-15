import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Transvection
import Langlands.Representation.Archimedean.RealGenericLargeReduction

/-!
# Irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-modules have an infinitesimal character

This file proves `RealGKModuleInfinitesimalCharacterStatement`: the center of `U(𝔤)`,
`𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, acts by scalars on every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module.

* Conjugation by every invertible real matrix fixes the center of `U(𝔤)`
  (`fixesCenter_of_det_ne_zero`). For `1 + (c - 1) e` with `e` idempotent this follows from a
  weight-space decomposition for `ad e` (`envMap_conjLie_idempotent`), and such matrices
  generate `GL_n(ℝ)` (diagonal matrices and transvections).
* Hence a central element acts by an operator commuting with `π` and `ρ`
  (`rho_mul_envelopingAction`).
* Admissibility gives this operator an eigenvector (`exists_eigenvector_of_commute`), and
  irreducibility makes it a scalar (`realGKModuleInfinitesimalCharacter`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

universe uV

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace InfinitesimalCharacter

/-! ## Weight spaces of an inner derivation and an automorphism -/

section Weight

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- The joint eigenspace on which `[h, ·]` acts by `m` and `σ` acts by `c ^ m`. -/
def weightSpace (h : B) (σ : B →ₐ[ℂ] B) (c : ℂ) (m : ℤ) : Submodule ℂ B where
  carrier := {a | h * a - a * h = (m : ℂ) • a ∧ σ a = c ^ m • a}
  add_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [mul_add, add_mul, smul_add, ← ha.1, ← hb.1]; abel
    · rw [map_add, ha.2, hb.2, smul_add]
  zero_mem' := by simp
  smul_mem' r a ha := by
    refine ⟨?_, ?_⟩
    · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ha.1, smul_comm]
    · rw [map_smul, ha.2, smul_comm]

theorem mem_weightSpace {h : B} {σ : B →ₐ[ℂ] B} {c : ℂ} {m : ℤ} {a : B} :
    a ∈ weightSpace h σ c m ↔ h * a - a * h = (m : ℂ) • a ∧ σ a = c ^ m • a :=
  Iff.rfl

theorem mul_mem_weightSpace {h : B} {σ : B →ₐ[ℂ] B} {c : ℂ} (hc : c ≠ 0) {m m' : ℤ} {a b : B}
    (ha : a ∈ weightSpace h σ c m) (hb : b ∈ weightSpace h σ c m') :
    a * b ∈ weightSpace h σ c (m + m') := by
  refine ⟨?_, ?_⟩
  · have : h * (a * b) - a * b * h = (h * a - a * h) * b + a * (h * b - b * h) := by noncomm_ring
    rw [this, ha.1, hb.1, smul_mul_assoc, mul_smul_comm, Int.cast_add, add_smul]
  · rw [map_mul, ha.2, hb.2, smul_mul_assoc, mul_smul_comm, smul_smul, zpow_add₀ hc, mul_comm]

/-- The sum of the weight spaces is closed under multiplication. -/
theorem mul_mem_iSup_weightSpace {h : B} {σ : B →ₐ[ℂ] B} {c : ℂ} (hc : c ≠ 0) {a b : B}
    (ha : a ∈ ⨆ m : ℤ, weightSpace h σ c m) (hb : b ∈ ⨆ m : ℤ, weightSpace h σ c m) :
    a * b ∈ ⨆ m : ℤ, weightSpace h σ c m := by
  refine Submodule.iSup_induction _ (motive := fun a => a * b ∈ ⨆ m : ℤ, weightSpace h σ c m)
    ha ?_ (by simp) ?_
  · intro m a ha
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ m : ℤ, weightSpace h σ c m)
      hb ?_ (by simp) ?_
    · intro m' b hb
      exact Submodule.mem_iSup_of_mem (m + m') (mul_mem_weightSpace hc ha hb)
    · intro b b' hb hb'
      rw [mul_add]; exact Submodule.add_mem _ hb hb'
  · intro a a' ha ha'
    rw [add_mul]; exact Submodule.add_mem _ ha ha'

/-- If `B` is the sum of the weight spaces, every element commuting with `h` is fixed by `σ`. -/
theorem fixed_of_commute {h : B} {σ : B →ₐ[ℂ] B} {c : ℂ}
    (hspan : ∀ u : B, u ∈ ⨆ m : ℤ, weightSpace h σ c m) {z : B} (hz : h * z = z * h) :
    σ z = z := by
  classical
  obtain ⟨f, hf, hfz⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ z).1 (hspan z)
  -- the inner derivation `[h, ·]`
  let D : Module.End ℂ B := LinearMap.mulLeft ℂ h - LinearMap.mulRight ℂ h
  have hD : ∀ a, D a = h * a - a * h := fun a => rfl
  have hind := Module.End.eigenspaces_iSupIndep D
  -- every component of nonzero weight vanishes
  have hzero : ∀ m : ℤ, m ≠ 0 → f m = 0 := by
    intro m hm
    have hsum : (f.sum fun i a => (i : ℂ) • a) = 0 := by
      have : D z = f.sum fun i a => (i : ℂ) • a := by
        rw [← hfz, Finsupp.sum, map_sum, Finsupp.sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hD, (hf i).1]
      rw [← this, hD, hz, sub_self]
    have hmem : (m : ℂ) • f m ∈ D.eigenspace (m : ℂ) := by
      rw [Module.End.mem_eigenspace_iff, map_smul, hD, (hf m).1]
    have hmem' : (m : ℂ) • f m ∈ ⨆ (μ : ℂ) (_ : μ ≠ (m : ℂ)), D.eigenspace μ := by
      have hrest : (m : ℂ) • f m =
          -∑ i ∈ f.support.erase m, (i : ℂ) • f i := by
        rw [eq_neg_iff_add_eq_zero, ← hsum, Finsupp.sum]
        by_cases hmS : m ∈ f.support
        · rw [← Finset.add_sum_erase _ _ hmS]
        · rw [Finsupp.notMem_support_iff.1 hmS, smul_zero, zero_add,
            Finset.erase_eq_of_notMem hmS]
      rw [hrest]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
      have hi' : (i : ℂ) ≠ (m : ℂ) := by
        rw [Ne, Int.cast_inj]; exact Finset.ne_of_mem_erase hi
      refine Submodule.mem_iSup_of_mem (i : ℂ) (Submodule.mem_iSup_of_mem hi' ?_)
      rw [Module.End.mem_eigenspace_iff, map_smul, hD, (hf i).1]
    have h0 : (m : ℂ) • f m = 0 :=
      (Submodule.disjoint_def.1 ((iSupIndep_def.1 hind) (m : ℂ))) _ hmem hmem'
    exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hm)
  rw [← hfz, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hf i).2]
  by_cases hi : i = 0
  · rw [hi, zpow_zero, one_smul]
  · rw [hzero i hi, smul_zero]

end Weight

/-! ## An induction principle for the universal enveloping algebra -/

section Enveloping

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Elements of `U(L)` are generated by scalars and `ι(L)` under sums and products. -/
@[elab_as_elim]
theorem envInduction {C : UniversalEnvelopingAlgebra ℂ L → Prop}
    (algebraMap : ∀ r : ℂ, C (algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) r))
    (ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι ℂ x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (u : UniversalEnvelopingAlgebra ℂ L) : C u := by
  let s : Subalgebra ℂ (UniversalEnvelopingAlgebra ℂ L) :=
    { carrier := {a | C a}
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  let of : L →ₗ⁅ℂ⁆ s :=
    { toFun := fun x => ⟨UniversalEnvelopingAlgebra.ι ℂ x, ι x⟩
      map_add' := fun x y => Subtype.ext (map_add (UniversalEnvelopingAlgebra.ι ℂ) x y)
      map_smul' := fun r x => Subtype.ext (map_smul (UniversalEnvelopingAlgebra.ι ℂ) r x)
      map_lie' := fun {x y} => Subtype.ext (by
        simp [LieRing.of_associative_ring_bracket]) }
  have of_id : AlgHom.id ℂ (UniversalEnvelopingAlgebra ℂ L) =
      s.val.comp (UniversalEnvelopingAlgebra.lift ℂ of) := by
    ext x
    simp [of]
  rw [← AlgHom.id_apply (R := ℂ) u, of_id]
  exact Subtype.prop (UniversalEnvelopingAlgebra.lift ℂ of u)

/-- If every generator `ι x` lies in the sum of the weight spaces, so does every element. -/
theorem mem_iSup_weightSpace_of_ι {h : UniversalEnvelopingAlgebra ℂ L}
    {σ : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ L} {c : ℂ}
    (hc : c ≠ 0)
    (hι : ∀ x : L, UniversalEnvelopingAlgebra.ι ℂ x ∈ ⨆ m : ℤ, weightSpace h σ c m)
    (u : UniversalEnvelopingAlgebra ℂ L) : u ∈ ⨆ m : ℤ, weightSpace h σ c m := by
  induction u using envInduction with
  | algebraMap r =>
    refine Submodule.mem_iSup_of_mem 0 ⟨?_, ?_⟩
    · simp [Algebra.commutes]
    · simp
  | ι x => exact hι x
  | mul a b ha hb => exact mul_mem_iSup_weightSpace hc ha hb
  | add a b ha hb => exact Submodule.add_mem _ ha hb

end Enveloping

/-! ## Inner automorphisms of an associative algebra and of its enveloping algebra -/

/-- For an idempotent `e` and `c ≠ 0`, `1 + (c⁻¹ - 1) e` is inverse to `1 + (c - 1) e`. -/
theorem idempotent_unit_mul {𝕜 B : Type*} [Field 𝕜] [Ring B] [Algebra 𝕜 B] {e : B}
    (he : e * e = e) {c : 𝕜} (hc : c ≠ 0) : (1 + (c - 1) • e) * (1 + (c⁻¹ - 1) • e) = 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, he, smul_mul_assoc, mul_smul_comm]
  have hcoef : (c - 1) + (c⁻¹ - 1) * c = 0 := by
    rw [sub_mul, inv_mul_cancel₀ hc, one_mul]; ring
  rw [add_assoc, show (c - 1) • e + (c⁻¹ - 1) • (e + (c - 1) • e) = ((c - 1) + (c⁻¹ - 1) * c) • e by
    module, hcoef, zero_smul, add_zero]

section Conj

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Conjugation `x ↦ w x w⁻¹` by a unit `w`, as an algebra endomorphism. -/
def unitConj (w : Aˣ) : A →ₐ[ℂ] A where
  toFun x := (w : A) * x * ((w⁻¹ : Aˣ) : A)
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by simp [Algebra.commutes, mul_assoc]

theorem unitConj_apply (w : Aˣ) (x : A) : unitConj w x = (w : A) * x * ((w⁻¹ : Aˣ) : A) :=
  rfl

theorem unitConj_mul (w₁ w₂ : Aˣ) : unitConj (w₁ * w₂) = (unitConj w₁).comp (unitConj w₂) := by
  ext x
  simp [unitConj_apply, mul_inv_rev, mul_assoc]

theorem unitConj_one : unitConj (1 : Aˣ) = AlgHom.id ℂ A := by
  ext x
  simp [unitConj_apply]

end Conj

section EnvMap

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- The algebra endomorphism of `U(L)` induced by a Lie algebra endomorphism of `L`. -/
def envMap (φ : L →ₗ⁅ℂ⁆ L) : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ L :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp φ)

theorem envMap_ι (φ : L →ₗ⁅ℂ⁆ L) (x : L) :
    envMap φ (UniversalEnvelopingAlgebra.ι ℂ x) = UniversalEnvelopingAlgebra.ι ℂ (φ x) := by
  simp [envMap]

theorem envMap_comp (φ ψ : L →ₗ⁅ℂ⁆ L) : envMap (φ.comp ψ) = (envMap φ).comp (envMap ψ) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  refine LieHom.ext fun x => ?_
  change envMap (φ.comp ψ) (UniversalEnvelopingAlgebra.ι ℂ x) =
    envMap φ (envMap ψ (UniversalEnvelopingAlgebra.ι ℂ x))
  rw [envMap_ι, envMap_ι, envMap_ι, LieHom.comp_apply]

theorem envMap_id : envMap (LieHom.id : L →ₗ⁅ℂ⁆ L) = AlgHom.id ℂ _ := by
  apply UniversalEnvelopingAlgebra.hom_ext
  refine LieHom.ext fun x => ?_
  change envMap (LieHom.id : L →ₗ⁅ℂ⁆ L) (UniversalEnvelopingAlgebra.ι ℂ x) =
    UniversalEnvelopingAlgebra.ι ℂ x
  rw [envMap_ι, LieHom.id_apply]

/-- The joint eigenspace in `L` on which `ad e` acts by `m` and `φ` by `c ^ m`. -/
def lieWeight (e : L) (φ : L →ₗ⁅ℂ⁆ L) (c : ℂ) (m : ℤ) : Submodule ℂ L where
  carrier := {y | ⁅e, y⁆ = (m : ℂ) • y ∧ φ y = c ^ m • y}
  add_mem' {a b} ha hb := ⟨by rw [lie_add, ha.1, hb.1, smul_add], by rw [map_add, ha.2, hb.2, smul_add]⟩
  zero_mem' := by simp
  smul_mem' r a ha := ⟨by rw [lie_smul, ha.1, smul_comm], by rw [map_smul, ha.2, smul_comm]⟩

/-- If `L` is the sum of the joint weight spaces of `ad e` and `φ`, with `φ` acting on weight
`m` by `c ^ m`, then the induced endomorphism of `U(L)` fixes the center of `U(L)`. -/
theorem envMap_fixes_center {e : L} {φ : L →ₗ⁅ℂ⁆ L} {c : ℂ} (hc : c ≠ 0)
    (hdec : ∀ x : L, x ∈ ⨆ m : ℤ, lieWeight e φ c m) {z : UniversalEnvelopingAlgebra ℂ L}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L)) : envMap φ z = z := by
  set ι := UniversalEnvelopingAlgebra.ι ℂ (L := L)
  have hgen : ∀ x : L, ι x ∈ ⨆ m : ℤ, weightSpace (ι e) (envMap φ) c m := by
    intro x
    refine Submodule.iSup_induction _ (motive := fun x => ι x ∈ ⨆ m : ℤ,
      weightSpace (ι e) (envMap φ) c m) (hdec x) ?_ (by simp) ?_
    · intro m y hy
      refine Submodule.mem_iSup_of_mem m ⟨?_, ?_⟩
      · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, hy.1, map_smul]
      · rw [envMap_ι, hy.2, map_smul]
    · intro a b ha hb
      rw [map_add]; exact Submodule.add_mem _ ha hb
  refine fixed_of_commute (mem_iSup_weightSpace_of_ι hc hgen) ?_
  exact (Subalgebra.mem_center_iff.1 hz) (ι e)

end EnvMap

/-! ## The Lie algebra `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` and its inner automorphisms -/

section Gl

variable {n : ℕ}

/-- The bracket of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` (extension of scalars) is the commutator of the algebra
`ℂ ⊗_ℝ M_n(ℝ)`. -/
theorem lie_eq_mul_sub (x y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) : ⁅x, y⁆ = x * y - y * x := by
  induction x using TensorProduct.inductionOn with
  | tmul a X =>
    induction y using TensorProduct.inductionOn with
    | tmul b Y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Ring.lie_def, TensorProduct.tmul_sub, mul_comm b a]
    | add y y' hy hy' =>
      calc ⁅a ⊗ₜ[ℝ] X, y + y'⁆ = ⁅a ⊗ₜ[ℝ] X, y⁆ + ⁅a ⊗ₜ[ℝ] X, y'⁆ :=
          lie_add (L := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (M := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) _ _ _
        _ = _ := by rw [hy, hy', mul_add, add_mul]; abel
  | add x x' hx hx' =>
    calc ⁅x + x', y⁆ = ⁅x, y⁆ + ⁅x', y⁆ :=
        add_lie (L := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (M := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) _ _ _
      _ = _ := by rw [hx, hx', mul_add, add_mul]; abel

/-- Conjugation by a unit of `ℂ ⊗_ℝ M_n(ℝ)`, as a Lie algebra automorphism of `𝔤`. -/
def conjLie (w : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) where
  toFun := unitConj w
  map_add' := map_add (unitConj w)
  map_smul' := map_smul (unitConj w)
  map_lie' {x y} := by
    simp only [lie_eq_mul_sub]
    rw [map_sub, map_mul, map_mul]

theorem conjLie_apply (w : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    conjLie w x = (w : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) * x *
      ((w⁻¹ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  rfl

theorem conjLie_mul (w₁ w₂ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) :
    conjLie (w₁ * w₂) = (conjLie w₁).comp (conjLie w₂) :=
  LieHom.ext fun x => by
    rw [LieHom.comp_apply]
    exact congrArg (fun f : _ →ₐ[ℂ] _ => f x) (unitConj_mul w₁ w₂)

theorem conjLie_one : conjLie (1 : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) = LieHom.id :=
  LieHom.ext fun x => by
    rw [LieHom.id_apply]
    exact congrArg (fun f : _ →ₐ[ℂ] _ => f x) unitConj_one

/-- Conjugation by `w = 1 + (c - 1) e`, `e` idempotent, fixes the center of `U(𝔤)`: `𝔤` is the
sum of the weight spaces of `ad e` with weights `0, ±1`, on which `Ad(w)` acts by `c ^ m`. -/
theorem envMap_conjLie_idempotent {e : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ} (he : e * e = e)
    {c : ℂ} (hc : c ≠ 0) (w : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hw : (w : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = 1 + (c - 1) • e)
    {z : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ))) :
    envMap (conjLie w) z = z := by
  set W := (w : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)
  set W' := ((w⁻¹ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)
  have hw' : W' = 1 + (c⁻¹ - 1) • e := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change W * _ = 1
    rw [hw]
    exact idempotent_unit_mul he hc
  have ee' : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have e'e : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have we : W * e = c • e := by
    rw [hw, add_mul, one_mul, smul_mul_assoc, he]; module
  have ew : e * W' = c⁻¹ • e := by
    rw [hw', mul_add, mul_one, mul_smul_comm, he]; module
  have we' : W * (1 - e) = 1 - e := by
    rw [hw, add_mul, one_mul, smul_mul_assoc, ee', smul_zero, add_zero]
  have ew' : (1 - e) * W' = 1 - e := by
    rw [hw', mul_add, mul_one, mul_smul_comm, e'e, smul_zero, add_zero]
  refine envMap_fixes_center (e := e) hc (fun x => ?_) hz
  have hx : x = e * x * e + e * x * (1 - e) + (1 - e) * x * e + (1 - e) * x * (1 - e) := by
    have h1 : e * x * e + e * x * (1 - e) = e * x := by rw [← mul_add, add_sub_cancel, mul_one]
    have h2 : (1 - e) * x * e + (1 - e) * x * (1 - e) = (1 - e) * x := by
      rw [← mul_add, add_sub_cancel, mul_one]
    rw [add_assoc (e * x * e + e * x * (1 - e)), h1, h2, ← add_mul, add_sub_cancel, one_mul]
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · refine Submodule.mem_iSup_of_mem 0 ⟨?_, ?_⟩
    · rw [lie_eq_mul_sub]
      have h1 : e * (e * x * e) = e * x * e := by rw [← mul_assoc, ← mul_assoc, he]
      have h2 : e * x * e * e = e * x * e := by rw [mul_assoc _ e e, he]
      rw [h1, h2, sub_self, Int.cast_zero, zero_smul]
    · rw [conjLie_apply, zpow_zero, one_smul]
      calc W * (e * x * e) * W' = (W * e) * x * (e * W') := by noncomm_ring
        _ = e * x * e := by
          rw [we, ew, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
            mul_inv_cancel₀ hc, one_smul]
  · refine Submodule.mem_iSup_of_mem 1 ⟨?_, ?_⟩
    · rw [lie_eq_mul_sub]
      have h1 : e * (e * x * (1 - e)) = e * x * (1 - e) := by
        rw [← mul_assoc, ← mul_assoc, he]
      have h2 : e * x * (1 - e) * e = 0 := by rw [mul_assoc _ (1 - e) e, e'e, mul_zero]
      rw [h1, h2, sub_zero, Int.cast_one, one_smul]
    · rw [conjLie_apply, zpow_one]
      calc W * (e * x * (1 - e)) * W' = (W * e) * x * ((1 - e) * W') := by noncomm_ring
        _ = c • (e * x * (1 - e)) := by rw [we, ew', smul_mul_assoc, smul_mul_assoc]
  · refine Submodule.mem_iSup_of_mem (-1) ⟨?_, ?_⟩
    · rw [lie_eq_mul_sub]
      have h1 : e * ((1 - e) * x * e) = 0 := by
        rw [← mul_assoc, ← mul_assoc, ee', zero_mul, zero_mul]
      have h2 : (1 - e) * x * e * e = (1 - e) * x * e := by rw [mul_assoc _ e e, he]
      rw [h1, h2, zero_sub, Int.cast_neg, Int.cast_one, neg_one_smul]
    · rw [conjLie_apply, zpow_neg_one]
      calc W * ((1 - e) * x * e) * W' = (W * (1 - e)) * x * (e * W') := by noncomm_ring
        _ = c⁻¹ • ((1 - e) * x * e) := by rw [we', ew, mul_smul_comm]
  · refine Submodule.mem_iSup_of_mem 0 ⟨?_, ?_⟩
    · rw [lie_eq_mul_sub]
      have h1 : e * ((1 - e) * x * (1 - e)) = 0 := by
        rw [← mul_assoc, ← mul_assoc, ee', zero_mul, zero_mul]
      have h2 : (1 - e) * x * (1 - e) * e = 0 := by rw [mul_assoc _ (1 - e) e, e'e, mul_zero]
      rw [h1, h2, sub_zero, Int.cast_zero, zero_smul]
    · rw [conjLie_apply, zpow_zero, one_smul]
      calc W * ((1 - e) * x * (1 - e)) * W' = (W * (1 - e)) * x * ((1 - e) * W') := by
            noncomm_ring
        _ = (1 - e) * x * (1 - e) := by rw [we', ew']

end Gl

/-! ## Real matrices whose conjugation fixes the center -/

section Matrices

variable {n : ℕ}

/-- The real `n × n` matrices `M` such that conjugation by `1 ⊗ M` (by any unit with this
underlying element) fixes the center of `U(𝔤)`, `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
def FixesCenter (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ w : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ,
    (w : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = Algebra.TensorProduct.includeRight M →
    ∀ z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)),
      envMap (conjLie w) z = z

theorem fixesCenter_one : FixesCenter (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro w hw z _
  have : w = 1 := Units.ext (by rw [hw, map_one, Units.val_one])
  rw [this, conjLie_one, envMap_id, AlgHom.id_apply]

theorem fixesCenter_mul {M N : Matrix (Fin n) (Fin n) ℝ} (hM : M.det ≠ 0)
    (hMf : FixesCenter M) (hNf : FixesCenter N) : FixesCenter (M * N) := by
  intro w hw z hz
  obtain ⟨u, hu⟩ : IsUnit (Algebra.TensorProduct.includeRight M :
      ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
    ((Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hM)).map _
  have h₂ : ((u⁻¹ * w : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) :
      ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = Algebra.TensorProduct.includeRight N := by
    rw [Units.val_mul, hw, map_mul, ← hu, Units.inv_mul_cancel_left]
  have hw' : w = u * (u⁻¹ * w) := (mul_inv_cancel_left u w).symm
  rw [hw', conjLie_mul, envMap_comp, AlgHom.comp_apply, hNf _ h₂ z hz, hMf _ hu z hz]

theorem fixesCenter_idempotent {e : Matrix (Fin n) (Fin n) ℝ} (he : e * e = e) {c : ℝ}
    (hc : c ≠ 0) : FixesCenter (1 + (c - 1) • e) := by
  intro w hw z hz
  refine envMap_conjLie_idempotent (e := Algebra.TensorProduct.includeRight e)
    (by rw [← map_mul, he]) (c := (c : ℂ)) (by exact_mod_cast hc) w ?_ hz
  have hcoe : ((c : ℂ) - 1) = algebraMap ℝ ℂ (c - 1) := by simp
  rw [hw, map_add, map_one, map_smul, hcoe, algebraMap_smul]

theorem det_ne_zero_of_idempotent {e : Matrix (Fin n) (Fin n) ℝ} (he : e * e = e) {c : ℝ}
    (hc : c ≠ 0) : (1 + (c - 1) • e).det ≠ 0 :=
  (Matrix.isUnit_det_of_right_inverse (idempotent_unit_mul he hc)).ne_zero

theorem diagonal_ite_eq (d : ℝ) (i : Fin n) :
    Matrix.diagonal (fun j => if j = i then d else 1) =
      1 + (d - 1) • Matrix.single i i (1 : ℝ) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai; simp
    · simp [hai, Ne.symm hai]
  · have h : ¬(i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab,
      Matrix.one_apply_ne hab, Matrix.single_apply, ite_eq_right_iff.2 (fun h' => absurd h' h), smul_zero, add_zero]

theorem fixesCenter_diagonal (D : Fin n → ℝ) (hD : ∀ i, D i ≠ 0) :
    FixesCenter (Matrix.diagonal D) := by
  classical
  have key : ∀ s : Finset (Fin n),
      FixesCenter (Matrix.diagonal fun j => if j ∈ s then D j else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (fixesCenter_one (n := n))
    | insert i s hi ih =>
      have hsplit : (Matrix.diagonal fun j => if j ∈ insert i s then D j else 1) =
          (Matrix.diagonal fun j => if j ∈ s then D j else 1) *
            Matrix.diagonal (fun j => if j = i then D i else 1) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [hsplit]
      refine fixesCenter_mul ?_ ih ?_
      · rw [Matrix.det_diagonal]
        refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
        split_ifs
        exacts [hD j, one_ne_zero]
      · rw [diagonal_ite_eq]
        exact fixesCenter_idempotent (by simp) (hD i)
  simpa using key Finset.univ

theorem fixesCenter_transvection (t : Matrix.TransvectionStruct (Fin n) ℝ) :
    FixesCenter t.toMatrix := by
  obtain ⟨i, j, hij, c⟩ := t
  set E : Matrix (Fin n) (Fin n) ℝ := Matrix.single j j 1 with hE
  set F : Matrix (Fin n) (Fin n) ℝ := Matrix.single i j 1 with hF
  have hEE : E * E = E := by simp [E]
  have hEF : E * F = 0 := Matrix.single_mul_single_of_ne (1 : ℝ) j j i (Ne.symm hij) 1
  have hFE : F * E = F := by simp [E, F]
  have hFF : F * F = 0 := Matrix.single_mul_single_of_ne (1 : ℝ) i j i (Ne.symm hij) 1
  set Q : Matrix (Fin n) (Fin n) ℝ := E - (c / 2) • F with hQdef
  have hQ : Q * Q = Q := by
    simp only [Q, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hEE, hEF, hFE, hFF, smul_zero]
    module
  have ht : Matrix.TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ =
      (1 + ((-1 : ℝ) - 1) • E) * (1 + ((-1 : ℝ) - 1) • Q) := by
    rw [Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection]
    have : Matrix.single i j c = c • F := by simp [F, Matrix.smul_single]
    rw [this]
    simp only [Q, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_sub,
      smul_sub, hEE, hEF, smul_zero]
    module
  rw [ht]
  exact fixesCenter_mul (det_ne_zero_of_idempotent hEE (by norm_num))
    (fixesCenter_idempotent hEE (by norm_num)) (fixesCenter_idempotent hQ (by norm_num))

/-- Conjugation by every invertible real matrix fixes the center of `U(𝔤)`. -/
theorem fixesCenter_of_det_ne_zero (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    FixesCenter M :=
  Matrix.diagonal_transvection_induction_of_det_ne_zero _ M hM
    (fun D hD => fixesCenter_diagonal D fun i => by
      rw [Matrix.det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ _))
    fixesCenter_transvection (fun _ _ hA _ hAf hBf => fixesCenter_mul hA hAf hBf)

end Matrices

/-! ## Compatibility of the `O(n)`-action with the action of `U(𝔤)` -/

section Compat

variable {n : ℕ}

/-- The unit `1 ⊗ k` of `ℂ ⊗_ℝ M_n(ℝ)` attached to `k ∈ O(n)`. -/
def orthUnit (k : Matrix.unitaryGroup (Fin n) ℝ) : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight :
    Matrix (Fin n) (Fin n) ℝ →ₐ[ℝ] ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ).toMonoidHom
    (Unitary.toUnits k)

theorem orthUnit_val (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (orthUnit k : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) =
      Algebra.TensorProduct.includeRight (k : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

theorem orthUnit_inv_val (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (((orthUnit k)⁻¹ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)ˣ) : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) =
      Algebra.TensorProduct.includeRight (star (k : Matrix (Fin n) (Fin n) ℝ)) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [orthUnit_val, ← map_mul, Unitary.mul_star_self_of_mem k.2, map_one]

theorem det_ne_zero_of_orth (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (k : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 :=
  (Matrix.isUnit_det_of_right_inverse (Unitary.mul_star_self_of_mem k.2)).ne_zero

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- `ρ(k) π(u) = π(Ad(k) u) ρ(k)` for all `u ∈ U(𝔤)`. -/
theorem rho_mul_envelopingAction
    (h4 : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (v : V),
      ρ k (π (1 ⊗ₜ X) v) =
        π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℝ) * X * (star k : Matrix (Fin n) (Fin n) ℝ)))
          (ρ k v))
    (k : Matrix.unitaryGroup (Fin n) ℝ)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :
    ρ k * envelopingAction π u = envelopingAction π (envMap (conjLie (orthUnit k)) u) * ρ k := by
  induction u using envInduction with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact (Algebra.commutes r (ρ k)).symm
  | ι x =>
    rw [envMap_ι, conjLie_apply, envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    induction x using TensorProduct.inductionOn with
    | tmul a X =>
      rw [orthUnit_val, orthUnit_inv_val, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      have hx : ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          a ⊗ₜ[ℝ] Y = a • (1 ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) := by
        intro Y; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      ext v
      rw [hx X, hx, map_smul, map_smul]
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, h4]
    | add x y hx hy =>
      simp only [map_add, mul_add, add_mul, hx, hy]
  | mul a b ha hb =>
    simp only [map_mul]
    rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb =>
    simp only [map_add, mul_add, add_mul, ha, hb]

end Compat

/-! ## Eigenvectors of endomorphisms commuting with an admissible `K`-action -/

section Eigen

variable {K : Type*} [Group K] [TopologicalSpace K] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Let `ρ` be an admissible representation of `K` in which every vector is `K`-finite and every
function `k ↦ ℓ(ρ(k) v)` is continuous. If `V ≠ 0`, every endomorphism `Z` of `V` commuting
with `ρ` has an eigenvector: `Z` acts on the finite-dimensional, nonzero space of
`K`-intertwiners from the `K`-span of a nonzero vector, where it has an eigenvector. -/
theorem exists_eigenvector_of_commute (ρ : Representation ℂ K V)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k : K => ℓ (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) (Z : Module.End ℂ V) (hZ : ∀ k : K, ρ k * Z = Z * ρ k)
    {v : V} (hv : v ≠ 0) : ∃ (c : ℂ) (x : V), x ≠ 0 ∧ Z x = c • x := by
  classical
  set W := FiniteVectors.orbitSpan ρ v with hWdef
  have : Module.Finite ℂ W := hfin v
  have hW : ∀ (k : K), ∀ w ∈ W, ρ k w ∈ W := fun k w hw =>
    (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k hw
  let b := Module.finBasis ℂ W
  -- the action of `K` on `W` and its matrices in the basis `b`
  let r : K → Module.End ℂ W := fun k => (ρ k).restrict (hW k)
  have hr : ∀ (k : K) (w : W), (r k w : V) = ρ k w := fun k w => rfl
  let τ : K →* Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    { toFun := fun k => LinearMap.toMatrix b b (r k)
      map_one' := by
        have : r 1 = 1 := LinearMap.ext fun w => Subtype.ext (by
          show ρ 1 (w : V) = (w : V)
          rw [map_one, Module.End.one_apply])
        rw [this, LinearMap.toMatrix_one]
      map_mul' := fun k k' => by
        have : r (k * k') = r k * r k' := LinearMap.ext fun w => Subtype.ext (by
          show ρ (k * k') (w : V) = ρ k (ρ k' (w : V))
          rw [map_mul, Module.End.mul_apply])
        rw [this, LinearMap.toMatrix_mul] }
  have hτ : ∀ k, τ k = LinearMap.toMatrix b b (r k) := fun k => rfl
  have hτc : Continuous τ := by
    refine continuous_matrix fun i j => ?_
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend (b.coord i)
    have : (fun k => τ k i j) = fun k => ℓ (ρ k (b j : V)) := by
      funext k
      rw [hτ, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, ← hℓ, LinearMap.comp_apply,
        Submodule.subtype_apply, hr]
    rw [this]
    exact hcont _ ℓ
  -- the inclusion of `W`, as an intertwiner from `τ`
  let T₀ : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hT₀ : T₀ ∈ gkIntertwiners ρ (Module.finrank ℂ W) τ := by
    show ∀ (k : K) (x : Fin (Module.finrank ℂ W) → ℂ), T₀ (τ k *ᵥ x) = ρ k (T₀ x)
    intro k x
    obtain ⟨y, rfl⟩ := b.equivFun.surjective x
    have h1 : τ k *ᵥ b.equivFun y = b.equivFun (r k y) := by
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, hτ]
      exact LinearMap.toMatrix_mulVec_repr b b (r k) y
    show W.subtype (b.equivFun.symm (τ k *ᵥ b.equivFun y)) =
      ρ k (W.subtype (b.equivFun.symm (b.equivFun y)))
    rw [h1, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hr k y
  have hT₀ne : T₀ ≠ 0 := by
    intro h
    apply hv
    have := LinearMap.congr_fun h (b.equivFun ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩)
    simpa [T₀] using this
  -- composition with `Z` on the finite-dimensional space of intertwiners
  let I := gkIntertwiners ρ (Module.finrank ℂ W) τ
  have : FiniteDimensional ℂ I := hadm _ τ hτc
  have : Nontrivial I := ⟨⟨⟨T₀, hT₀⟩, 0, fun h => hT₀ne (congrArg Subtype.val h)⟩⟩
  let Φ : Module.End ℂ I :=
    { toFun := fun T => ⟨Z ∘ₗ (T : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V), by
        show ∀ (k : K) (x : Fin (Module.finrank ℂ W) → ℂ),
          Z ((T : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V) (τ k *ᵥ x)) =
            ρ k (Z ((T : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V) x))
        intro k x
        rw [T.2 k x, ← Module.End.mul_apply, ← hZ k, Module.End.mul_apply]⟩
      map_add' := fun S T => Subtype.ext (LinearMap.ext fun x => by simp)
      map_smul' := fun a T => Subtype.ext (LinearMap.ext fun x => by simp) }
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Φ
  obtain ⟨T, hT⟩ := hc.exists_hasEigenvector
  have hTc : Φ T = c • T := hT.apply_eq_smul
  have hTne : (T : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V) ≠ 0 := fun h => hT.2 (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x, (T : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V) x ≠ 0 := by
    by_contra! h
    exact hTne (LinearMap.ext h)
  refine ⟨c, (T : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] V) x, hx, ?_⟩
  exact LinearMap.congr_fun (congrArg Subtype.val hTc) x

end Eigen

/-! ## The main theorem -/

/-- **Irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-modules have an infinitesimal character.** An
element `z` of the center of `U(𝔤)` acts by an operator `Z` commuting with `π` (as `z` is
central) and with `ρ` (as `Ad(k)` fixes `z`). By admissibility `Z` has an eigenvector; its
eigenspace is a nonzero `(𝔤, K)`-submodule, hence everything by irreducibility. -/
theorem realGKModuleInfinitesimalCharacter :
    RealGKModuleInfinitesimalCharacterStatement.{uV} := by
  intro n V _ _ ρ π hgk hirr hadm z hz
  set Z := envelopingAction π z with hZdef
  have hZπ : ∀ X, π X * Z = Z * π X := by
    intro X
    have h := congrArg (envelopingAction π)
      ((Subalgebra.mem_center_iff.1 hz) (UniversalEnvelopingAlgebra.ι ℂ X))
    rwa [map_mul, map_mul, envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply] at h
  have hZρ : ∀ k, ρ k * Z = Z * ρ k := by
    intro k
    rw [hZdef, rho_mul_envelopingAction hgk.2.2.2 k z,
      fixesCenter_of_det_ne_zero _ (det_ne_zero_of_orth k) (orthUnit k) (orthUnit_val k) z hz]
  have := hirr.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨c, x, hx, hZx⟩ := exists_eigenvector_of_commute ρ hgk.1 hgk.2.1 hadm Z hZρ hv
  refine ⟨c, ?_⟩
  set E := LinearMap.ker (Z - algebraMap ℂ (Module.End ℂ V) c) with hE
  have hmem : ∀ w, w ∈ E ↔ Z w = c • w := by
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  have htop : E = ⊤ := by
    refine (hirr.2 E (fun k w hw => ?_) (fun X w hw => ?_)).resolve_left fun hbot => hx ?_
    · rw [hmem] at hw ⊢
      rw [← Module.End.mul_apply, ← hZρ k, Module.End.mul_apply, hw, map_smul]
    · rw [hmem] at hw ⊢
      rw [← Module.End.mul_apply, ← hZπ X, Module.End.mul_apply, hw, map_smul]
    · have : x ∈ E := (hmem x).2 hZx
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).1 this
  refine LinearMap.ext fun w => ?_
  rw [Module.algebraMap_end_apply]
  exact (hmem w).1 (by rw [htop]; exact Submodule.mem_top)

end InfinitesimalCharacter

end Langlands.Archimedean
