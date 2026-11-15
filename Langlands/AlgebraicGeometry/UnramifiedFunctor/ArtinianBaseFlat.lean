import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseChain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Minpoly.Field

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing Polynomial

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}}

section LocalNil

/-- A ring with a surjection onto a field whose kernel consists of nilpotent elements is
local. -/
lemma isLocalRing_of_ker_nil {P L : Type*} [CommRing P] [Field L] (φ : P →+* L)
    (hφ : Function.Surjective φ) (h : ∀ x, φ x = 0 → IsNilpotent x) : IsLocalRing P := by
  have : Nontrivial P := φ.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  by_cases hx : φ x = 0
  · exact Or.inr (h x hx).isUnit_one_sub
  · left
    obtain ⟨y, hy⟩ := hφ (φ x)⁻¹
    have h1 : φ (x * y - 1) = 0 := by rw [map_sub, map_mul, hy, mul_inv_cancel₀ hx, map_one, sub_self]
    have := (h _ h1).isUnit_one_add
    rw [add_sub_cancel] at this
    exact isUnit_of_mul_isUnit_left this

end LocalNil

section FlatExt

/-- Finite flat extensions with prescribed residue field. Let `C` be a local artinian ring with
a surjection `π : C → ℓ` onto a field, and `N` a finite extension of `ℓ`. There is a local
artinian `C`-algebra `P`, finite and free over `C`, with a surjection `P → N` compatible with
`π`. Proof by induction on `[N : ℓ]`: adjoin a root of a monic lift of the minimal polynomial
of an element of `N \ ℓ`. -/
theorem flatExt : ∀ (n : ℕ) (C ℓ N : Type u) [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    [Algebra R C] [Field ℓ] [Algebra R ℓ] [Field N] [Algebra R N] [Algebra ℓ N]
    [IsScalarTower R ℓ N] [FiniteDimensional ℓ N] (π : C →ₐ[R] ℓ), Function.Surjective π →
    Module.finrank ℓ N ≤ n →
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra C P) (_ : Algebra R P)
      (_ : IsScalarTower R C P), IsLocalRing P ∧ IsArtinianRing P ∧ Module.Free C P ∧
        Module.Finite C P ∧ ∃ πP : P →ₐ[R] N, Function.Surjective πP ∧
          πP.comp (IsScalarTower.toAlgHom R C P) = (IsScalarTower.toAlgHom R ℓ N).comp π := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C ℓ N _ _ _ _ _ _ _ _ _ _ _ π hπ hn
  by_cases h1 : Module.finrank ℓ N = 1
  · refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, (IsScalarTower.toAlgHom R ℓ N).comp π, ?_, ?_⟩
    · have hsurj : Function.Surjective (algebraMap ℓ N) := by
        intro x
        have : (⊥ : Subalgebra ℓ N) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
        have hx : x ∈ (⊥ : Subalgebra ℓ N) := this ▸ Algebra.mem_top
        exact Algebra.mem_bot.mp hx
      exact hsurj.comp hπ
    · ext; rfl
  -- pick `θ ∈ N` not in `ℓ`
  have hpos : 0 < Module.finrank ℓ N := Module.finrank_pos
  obtain ⟨θ, hθ⟩ : ∃ θ : N, θ ∉ (algebraMap ℓ N).range := by
    by_contra! H
    apply h1
    have : (⊥ : Subalgebra ℓ N) = ⊤ := eq_top_iff.mpr fun x _ ↦ Algebra.mem_bot.mpr (H x)
    exact Subalgebra.bot_eq_top_iff_finrank_eq_one.mp this
  have hθi : IsIntegral ℓ θ := IsIntegral.of_finite ℓ θ
  let g := minpoly ℓ θ
  have hg2 : 2 ≤ g.natDegree := (minpoly.two_le_natDegree_iff hθi).mpr hθ
  have hgm : g.Monic := minpoly.monic hθi
  have : Fact (Irreducible g) := ⟨minpoly.irreducible hθi⟩
  obtain ⟨ĝ, hĝmap, -, hĝm⟩ := lifts_and_natDegree_eq_and_monic
    (f := π.toRingHom) (map_surjective _ hπ g) hgm
  let P₁ := AdjoinRoot ĝ
  let ℓ₁ := AdjoinRoot g
  have : Module.Free C P₁ := hĝm.free_adjoinRoot
  have : Module.Finite C P₁ := hĝm.finite_adjoinRoot
  have : IsArtinianRing P₁ := IsArtinianRing.of_finite C P₁
  -- the map `P₁ → ℓ₁`
  have hev : ĝ.eval₂ ((AdjoinRoot.of g).comp π.toRingHom) (AdjoinRoot.root g) = 0 := by
    rw [← eval₂_map, hĝmap]
    exact AdjoinRoot.eval₂_root g
  let π₁r : P₁ →+* ℓ₁ := AdjoinRoot.lift ((AdjoinRoot.of g).comp π.toRingHom) _ hev
  let π₁ : P₁ →ₐ[R] ℓ₁ :=
    { π₁r with
      commutes' := fun r ↦ by
        change π₁r (AdjoinRoot.of ĝ (algebraMap R C r)) = AdjoinRoot.of g (algebraMap R ℓ r)
        rw [AdjoinRoot.lift_of]
        simp }
  have hπ₁mk : ∀ q : C[X], π₁ (AdjoinRoot.mk ĝ q) = AdjoinRoot.mk g (q.map π.toRingHom) := by
    intro q
    change π₁r _ = _
    rw [AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    rfl
  have hπ₁s : Function.Surjective π₁ := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨q, rfl⟩ := map_surjective π.toRingHom hπ p
    exact ⟨AdjoinRoot.mk ĝ q, hπ₁mk q⟩
  have hπ₁of : π₁.comp (IsScalarTower.toAlgHom R C P₁) =
      (IsScalarTower.toAlgHom R ℓ ℓ₁).comp π := by
    ext c
    change π₁r (AdjoinRoot.of ĝ c) = AdjoinRoot.of g (π c)
    rw [AdjoinRoot.lift_of]
    rfl
  -- the kernel of `P₁ → ℓ₁` is nil
  have hmnil : IsNilpotent ((maximalIdeal C).map (algebraMap C P₁)) := by
    obtain ⟨k, hk⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
    exact ⟨k, by rw [← Ideal.map_pow, hk, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
  have hkerπ : RingHom.ker π = maximalIdeal C :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
  have hnil : ∀ x : P₁, π₁ x = 0 → IsNilpotent x := by
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [hπ₁mk, AdjoinRoot.mk_eq_zero] at hx
    obtain ⟨h, hh⟩ := hx
    obtain ⟨h', rfl⟩ := map_surjective π.toRingHom hπ h
    have hf : AdjoinRoot.mk ĝ f = AdjoinRoot.mk ĝ (f - ĝ * h') := by
      rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
    have hcoeff : ∀ i, (f - ĝ * h').coeff i ∈ maximalIdeal C := by
      intro i
      rw [← hkerπ, RingHom.mem_ker]
      have : (f - ĝ * h').map π.toRingHom = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hĝmap, hh, sub_self]
      have h0 := congrArg (fun p ↦ p.coeff i) this
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h0
      exact h0
    rw [hf]
    obtain ⟨k, hk⟩ := hmnil
    refine ⟨k, ?_⟩
    have hmem : AdjoinRoot.mk ĝ (f - ĝ * h') ∈ (maximalIdeal C).map (algebraMap C P₁) := by
      rw [← AdjoinRoot.aeval_eq, aeval_eq_sum_range]
      refine Ideal.sum_mem _ fun i _ ↦ ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoeff i))
    have := Ideal.pow_mem_pow hmem k
    rw [hk] at this
    simpa using this
  have : IsLocalRing P₁ := isLocalRing_of_ker_nil π₁.toRingHom hπ₁s hnil
  -- `N` over `ℓ₁`
  let ι : ℓ₁ →+* N := AdjoinRoot.lift (algebraMap ℓ N) θ (by
    rw [← aeval_def]; exact minpoly.aeval ℓ θ)
  let : Algebra ℓ₁ N := ι.toAlgebra
  have : IsScalarTower R ℓ₁ N := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R N r = ι (AdjoinRoot.of g (algebraMap R ℓ r))
    rw [AdjoinRoot.lift_of, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower ℓ ℓ₁ N := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap ℓ N r = ι (AdjoinRoot.of g r)
    rw [AdjoinRoot.lift_of]
  have : FiniteDimensional ℓ₁ N := Module.Finite.of_restrictScalars_finite ℓ ℓ₁ N
  have hrank : Module.finrank ℓ ℓ₁ * Module.finrank ℓ₁ N = Module.finrank ℓ N :=
    Module.finrank_mul_finrank ℓ ℓ₁ N
  have hrank₁ : Module.finrank ℓ ℓ₁ = g.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hgm.ne_zero)]
    rfl
  have hlt : Module.finrank ℓ₁ N < n := by
    have hN1 : 0 < Module.finrank ℓ₁ N := Module.finrank_pos
    rw [hrank₁] at hrank
    nlinarith
  obtain ⟨P, _, _, _, _, hPl, hPa, hPfree, hPfin, πP, hπPs, hπP⟩ :=
    ih _ hlt P₁ ℓ₁ N π₁ hπ₁s le_rfl
  let : Algebra C P := ((algebraMap P₁ P).comp (algebraMap C P₁)).toAlgebra
  have : IsScalarTower C P₁ P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R C P := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R P r = algebraMap P₁ P (algebraMap C P₁ (algebraMap R C r))
    rw [← IsScalarTower.algebraMap_apply R C P₁ r, ← IsScalarTower.algebraMap_apply R P₁ P r]
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, hPl, hPa,
    Module.Free.trans (R := C) (S := P₁) (M := P), Module.Finite.trans P₁ P, πP, hπPs, ?_⟩
  ext c
  have h1 := congrArg (fun f ↦ f (algebraMap C P₁ c)) hπP
  have h2 := congrArg (fun f ↦ f c) hπ₁of
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 ⊢
  rw [IsScalarTower.algebraMap_apply C P₁ P, h1, h2]
  exact (IsScalarTower.algebraMap_apply ℓ ℓ₁ N (π c)).symm

end FlatExt

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
