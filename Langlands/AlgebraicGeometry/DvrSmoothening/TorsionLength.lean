import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Torsion lengths of finite modules over a discrete valuation ring -/

namespace Langlands.AlgebraicGeometry.DvrSmoothening

open Module Submodule

/-- The length of the torsion submodule of a module. -/
noncomputable def torsionLength (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (Submodule.torsion R M)

section General

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem mem_torsion_map {f : M →ₗ[R] N} {x : M} (hx : x ∈ Submodule.torsion R M) :
    f x ∈ Submodule.torsion R N := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, ?_⟩
  change (a : R) • f x = 0
  rw [← map_smul]
  change f (a • x) = 0
  rw [ha, map_zero]

/-- The restriction of a linear map to torsion submodules. -/
noncomputable def torsionMap (f : M →ₗ[R] N) :
    Submodule.torsion R M →ₗ[R] Submodule.torsion R N :=
  (f.comp (Submodule.torsion R M).subtype).codRestrict _ fun x => mem_torsion_map (f := f) x.2

@[simp] theorem torsionMap_apply (f : M →ₗ[R] N) (x : Submodule.torsion R M) :
    (torsionMap f x : N) = f x := rfl

theorem torsionLength_le_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    torsionLength R M ≤ torsionLength R N :=
  Module.length_le_of_injective (torsionMap f) fun _ _ hxy =>
    Subtype.ext (hf (congrArg Subtype.val hxy))

theorem torsionLength_congr (e : M ≃ₗ[R] N) : torsionLength R M = torsionLength R N :=
  le_antisymm (torsionLength_le_of_injective e.toLinearMap e.injective)
    (torsionLength_le_of_injective e.symm.toLinearMap e.symm.injective)

theorem torsionLength_eq_zero_iff : torsionLength R M = 0 ↔ Submodule.torsion R M = ⊥ := by
  rw [torsionLength, Module.length_eq_zero_iff, Submodule.subsingleton_iff_eq_bot]

end General

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A finite torsion module over a discrete valuation ring has finite length. -/
theorem isFiniteLength_of_isTorsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    IsFiniteLength R M := by
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have haM : Module.IsTorsionBy R M a := fun x =>
    (Submodule.mem_annihilator.mp ha) x Submodule.mem_top
  let I : Ideal R := Ideal.span {a}
  have haI : Module.IsTorsionBySet R M I :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr haM
  let : Module (R ⧸ I) M := haI.module
  have : IsScalarTower R (R ⧸ I) M := haI.isScalarTower
  have : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R _ _
  have hfin : IsFiniteLength R (R ⧸ I) := isFiniteLength_quotient_span_singleton R ha0
  have : IsArtinian R (R ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R inferInstance
  have : IsArtinian R M :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

theorem isFiniteLength_torsion [Module.Finite R M] :
    IsFiniteLength R (Submodule.torsion R M) :=
  isFiniteLength_of_isTorsion Submodule.torsion_isTorsion

theorem torsionLength_ne_top [Module.Finite R M] : torsionLength R M ≠ ⊤ :=
  Module.length_ne_top_iff.mpr isFiniteLength_torsion

theorem torsionLength_eq_zero_iff_free [Module.Finite R M] :
    torsionLength R M = 0 ↔ Module.Free R M := by
  rw [torsionLength_eq_zero_iff, ← Submodule.isTorsionFree_iff_torsion_eq_bot,
    Module.free_iff_isTorsionFree]

end DVR

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {F F' : Type*} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']

/-- Lattice comparison: over a discrete valuation ring with uniformizer `ϖ`, let `F` be a finite
module and `θ : F' → F` a linear map with image inside `ϖ F`, let `N ⊆ F` lie in the image of `θ`,
and let `N' ⊆ F'` contain `θ⁻¹ N` and lie in its saturation. If `F ⧸ N` has non-zero torsion, then
the torsion of `F' ⧸ N'` is strictly shorter than that of `F ⧸ N`. -/
theorem torsionLength_lt_of_lattice [Module.Finite R F] {ϖ : R} (hϖ : Irreducible ϖ)
    (θ : F' →ₗ[R] F) (hθϖ : ∀ x, ∃ y, θ x = ϖ • y)
    (N : Submodule R F) (N' : Submodule R F')
    (hN : N ≤ LinearMap.range θ) (h1 : N.comap θ ≤ N')
    (h2 : ∀ x ∈ N', ∃ n : ℕ, ϖ ^ n • x ∈ N.comap θ)
    (hT : Submodule.torsion R (F ⧸ N) ≠ ⊥) :
    torsionLength R (F' ⧸ N') < torsionLength R (F ⧸ N) := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  set N0 := N.comap θ with hN0
  -- Step 1: passing from `N0` to the larger `N'` does not lengthen the torsion.
  have step1 : torsionLength R (F' ⧸ N') ≤ torsionLength R (F' ⧸ N0) := by
    let q : F' ⧸ N0 →ₗ[R] F' ⧸ N' := N0.mapQ N' LinearMap.id h1
    apply Module.length_le_of_surjective (torsionMap q)
    rintro ⟨xb, hx⟩
    obtain ⟨x, rfl⟩ := N'.mkQ_surjective xb
    obtain ⟨a, ha⟩ := hx
    have hax : (a : R) • x ∈ N' := by
      rw [← Submodule.Quotient.mk_eq_zero N']
      exact ha
    obtain ⟨n, hn⟩ := h2 _ hax
    have hmem : (ϖ ^ n * a : R) ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (pow_ne_zero n hϖ0)
        (nonZeroDivisors.coe_ne_zero a))
    refine ⟨⟨N0.mkQ x, ⟨⟨_, hmem⟩, ?_⟩⟩, ?_⟩
    · change (ϖ ^ n * a : R) • N0.mkQ x = 0
      rw [← map_smul, mul_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hn
    · rfl
  -- Step 2: the map induced by `θ` on quotients is injective.
  let θb : F' ⧸ N0 →ₗ[R] F ⧸ N := N0.mapQ N θ le_rfl
  have hθb : Function.Injective θb := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.mkQ_map_self]
  set T := Submodule.torsion R (F ⧸ N) with hTdef
  let P : Submodule R T := (LinearMap.range θb).comap T.subtype
  have hfinT : IsFiniteLength R T := isFiniteLength_torsion
  have hTA : IsArtinian R T := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinT).2
  have hTN : IsNoetherian R T := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinT).1
  have step2 : torsionLength R (F' ⧸ N0) ≤ Module.length R P := by
    let g : Submodule.torsion R (F' ⧸ N0) →ₗ[R] P :=
      (torsionMap θb).codRestrict P fun x => ⟨x.1, rfl⟩
    apply Module.length_le_of_injective g
    intro x y hxy
    apply Subtype.ext
    apply hθb
    exact congrArg (fun z : P => ((z : T) : F ⧸ N)) hxy
  -- Step 3: `P` is a proper submodule of `T`.
  have hP : P ≠ ⊤ := by
    intro hPtop
    let S : Submodule R F := T.comap N.mkQ
    have hS : S ≤ (Ideal.span {ϖ}) • S := by
      intro s hs
      have hsT : N.mkQ s ∈ T := hs
      have hsP : (⟨N.mkQ s, hsT⟩ : T) ∈ P := hPtop ▸ Submodule.mem_top
      obtain ⟨xb, hxb⟩ := hsP
      obtain ⟨x, rfl⟩ := N0.mkQ_surjective xb
      have hdiff : s - θ x ∈ N := by
        rw [← Submodule.Quotient.mk_eq_zero N, Submodule.Quotient.mk_sub]
        have : θb (N0.mkQ x) = N.mkQ s := hxb
        rw [sub_eq_zero]
        exact this.symm
      obtain ⟨x', hx'⟩ := hN hdiff
      obtain ⟨y, hy⟩ := hθϖ (x' + x)
      have hsy : s = ϖ • y := by
        rw [← hy, map_add, hx', sub_add_cancel]
      have hyS : y ∈ S := by
        change N.mkQ y ∈ T
        have hs' : ϖ • N.mkQ y ∈ T := by
          rw [← map_smul, ← hsy]
          exact hsT
        obtain ⟨a, ha⟩ := hs'
        refine ⟨⟨(a : R) * ϖ, mem_nonZeroDivisors_of_ne_zero
          (mul_ne_zero (nonZeroDivisors.coe_ne_zero a) hϖ0)⟩, ?_⟩
        change ((a : R) * ϖ) • N.mkQ y = 0
        rw [mul_smul]
        exact ha
      rw [hsy]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) hyS
    have hSfg : S.FG := IsNoetherian.noetherian S
    have hjac : Ideal.span {ϖ} ≤ (⊥ : Ideal R).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
        Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    have hS0 : S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ S hSfg hS hjac
    apply hT
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨w, rfl⟩ := N.mkQ_surjective z
    have hw : w ∈ S := hz
    rw [hS0, Submodule.mem_bot] at hw
    rw [hw, map_zero]
    exact Submodule.zero_mem _
  have step3 : Module.length R P < Module.length R T := Submodule.length_lt hP
  calc torsionLength R (F' ⧸ N') ≤ torsionLength R (F' ⧸ N0) := step1
    _ ≤ Module.length R P := step2
    _ < Module.length R T := step3

end Lattice

end Langlands.AlgebraicGeometry.DvrSmoothening
