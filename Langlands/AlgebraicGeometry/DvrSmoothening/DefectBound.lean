import Langlands.AlgebraicGeometry.DvrSmoothening.DefectBoundStatement
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Boundedness of the defect of smoothness -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

section Torsion

variable {R' : Type*} [CommRing R'] [IsDomain R'] {M : Type*} [AddCommGroup M] [Module R' M]

/-- Let `G : R'^m → M` be surjective and `H : M → R'^m` with `G ∘ H = c` for some `c ≠ 0` in a
domain `R'`. Then the torsion submodule of `M` has length at most `m · ord(c)`, where
`ord(c)` is the length of `R' ⧸ c R'`. -/
theorem length_torsion_le_of_comp_eq_smul {m : ℕ} (G : (Fin m → R') →ₗ[R'] M)
    (H : M →ₗ[R'] (Fin m → R')) (hG : Function.Surjective G) {c : R'} (hc : c ≠ 0)
    (hGH : G ∘ₗ H = c • LinearMap.id) :
    Module.length R' (Submodule.torsion R' M) ≤ m * Ring.ord R' c := by
  have hkill : ∀ x ∈ Submodule.torsion R' M, c • x = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := hx
    have hHx : H x = 0 := by
      funext i
      have h0 : (a : R') * H x i = 0 := by
        have := congrFun (congrArg H ha) i
        simpa [Submonoid.smul_def] using this
      exact (mul_eq_zero.mp h0).resolve_left (nonZeroDivisors.coe_ne_zero a)
    have := LinearMap.congr_fun hGH x
    simp only [LinearMap.comp_apply, hHx, map_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at this
    exact this.symm
  let cM : Submodule R' M := LinearMap.range (c • LinearMap.id : M →ₗ[R'] M)
  let cF : Submodule R' (Fin m → R') :=
    LinearMap.range (c • LinearMap.id : (Fin m → R') →ₗ[R'] (Fin m → R'))
  have h1 : Module.length R' (Submodule.torsion R' M) ≤ Module.length R' (M ⧸ cM) := by
    apply Module.length_le_of_injective (cM.mkQ ∘ₗ (Submodule.torsion R' M).subtype)
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, rfl⟩ := h0
    have hy : y ∈ Submodule.torsion R' M := by
      obtain ⟨a, ha⟩ := hx
      refine ⟨⟨(a : R') * c, mem_nonZeroDivisors_of_ne_zero
        (mul_ne_zero (nonZeroDivisors.coe_ne_zero a) hc)⟩, ?_⟩
      change ((a : R') * c) • y = 0
      rw [mul_smul]
      simpa [Submonoid.smul_def] using ha
    apply Subtype.ext
    simpa using hkill y hy
  have h2 : Module.length R' (M ⧸ cM) ≤ Module.length R' ((Fin m → R') ⧸ cF) := by
    refine Module.length_le_of_surjective (cF.mapQ cM G ?_) ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨G y, by simp⟩
    · intro z
      obtain ⟨z, rfl⟩ := cM.mkQ_surjective z
      obtain ⟨y, rfl⟩ := hG z
      exact ⟨cF.mkQ y, rfl⟩
  have hcF : cF = Submodule.pi Set.univ (fun _ : Fin m => (Ideal.span {c} : Submodule R' R')) := by
    ext x
    simp only [cF, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_pi, Set.mem_univ, true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by simp [mul_comm]⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext fun i => by simp [← hy i, mul_comm]⟩
  have h3 : Module.length R' ((Fin m → R') ⧸ cF) = m * Ring.ord R' c := by
    rw [hcF, (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
    simp [Ring.ord]
  calc Module.length R' (Submodule.torsion R' M) ≤ Module.length R' (M ⧸ cM) := h1
    _ ≤ Module.length R' ((Fin m → R') ⧸ cF) := h2
    _ = m * Ring.ord R' c := h3

end Torsion

section Splitting

/-- Let `M` be a finitely presented `A`-module whose localization `M[1/s]` is projective over
`A[1/s]`, and let `v` generate `M`. Then the surjection `A^m → M` defined by `v` has a section up
to a power of `s`: there are `h : M → A^m` and `e` with `(∑ vᵢ) ∘ h = sᵉ`. -/
theorem exists_comp_eq_pow_smul {A B M MB : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (s : A) [IsLocalization.Away s B] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] [AddCommGroup MB] [Module A MB] [Module B MB]
    [IsScalarTower A B MB] [Module.Projective B MB] (L : M →ₗ[A] MB) [IsLocalizedModule (Submonoid.powers s) L]
    {m : ℕ} (v : Fin m → M) (hv : Submodule.span A (Set.range v) = ⊤) :
    ∃ (h : M →ₗ[A] (Fin m → A)) (e : ℕ),
      Fintype.linearCombination A v ∘ₗ h = s ^ e • LinearMap.id := by
  classical
  let S := Submonoid.powers s
  let gB : (Fin m → B) →ₗ[B] MB := Fintype.linearCombination B (L ∘ v)
  have hgB : Function.Surjective gB := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Set.range_comp]
    exact span_eq_top_of_isLocalizedModule B S L hv
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property gB LinearMap.id hgB
  let ℓ : (Fin m → A) →ₗ[A] (Fin m → B) :=
    LinearMap.pi fun i => Algebra.linearMap A B ∘ₗ LinearMap.proj i
  obtain ⟨h, t, ht⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S ℓ (σ.restrictScalars A ∘ₗ L)
  have hcomp : ∀ a, gB (ℓ a) = L (Fintype.linearCombination A v a) := by
    intro a
    simp only [gB, ℓ, Fintype.linearCombination_apply, map_sum, LinearMap.map_smul,
      LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply,
      Function.comp_apply, algebraMap_smul]
  have hx : ∀ x, L (Fintype.linearCombination A v (h x) - (t : A) • x) = 0 := by
    intro x
    rw [map_sub, ← hcomp, LinearMap.map_smul]
    have := LinearMap.congr_fun ht x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.coe_restrictScalars] at this
    rw [this, Submonoid.smul_def, LinearMap.map_smul_of_tower, ← LinearMap.comp_apply gB σ, hσ,
      LinearMap.id_apply, sub_self]
  choose u hu using fun i => (IsLocalizedModule.eq_zero_iff S L).mp (hx (v i))
  let U : A := ∏ i, (u i : A)
  have hU : U ∈ S := Submonoid.prod_mem _ fun i _ => (u i).2
  obtain ⟨e, he⟩ := Submonoid.mem_powers_iff _ _ |>.mp (S.mul_mem hU t.2)
  refine ⟨U • h, e, LinearMap.ext_on_range hv fun i => ?_⟩
  have hui : (u i : A) • (Fintype.linearCombination A v (h (v i)) - (t : A) • v i) = 0 := by
    simpa [Submonoid.smul_def] using hu i
  have hUi : U • (Fintype.linearCombination A v (h (v i)) - (t : A) • v i) = 0 := by
    have : U = (∏ j ∈ Finset.univ.erase i, (u j : A)) * (u i : A) := by
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [this, mul_smul, hui, smul_zero]
  rw [smul_sub, sub_eq_zero] at hUi
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, LinearMap.id_apply]
  rw [hUi, ← mul_smul, he]

end Splitting

/-- The defect of smoothness is bounded on all points of ramification index one: BLR §3.3,
Proposition 3 in the form of §3.6. -/
theorem defectBoundStatement : DefectBoundStatement.{u} := by
  intro R A _ _ _ _ _ _ ϖ hϖ hsm
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite A _
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := Ω[A⁄R])
  obtain ⟨h, e, hh⟩ := exists_comp_eq_pow_smul (B := Localization.Away (algebraMap R A ϖ))
    (algebraMap R A ϖ)
    (KaehlerDifferential.map R R A (Localization.Away (algebraMap R A ϖ))) v hv
  refine ⟨m * e, ?_⟩
  intro R' _ _ _ _ _ hram φ
  let : Algebra A R' := φ.toRingHom.toAlgebra
  have hϖ' : Irreducible (algebraMap R R' ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hram.1, hϖ.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  let eF := TensorProduct.piScalarRight A R' R' (Fin m)
  let G : (Fin m → R') →ₗ[R'] R' ⊗[A] Ω[A⁄R] :=
    (Fintype.linearCombination A v).baseChange R' ∘ₗ eF.symm.toLinearMap
  let H : R' ⊗[A] Ω[A⁄R] →ₗ[R'] (Fin m → R') := eF.toLinearMap ∘ₗ h.baseChange R'
  have hG : Function.Surjective G := by
    have hsurj : Function.Surjective (Fintype.linearCombination A v) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
    exact (LinearMap.lTensor_surjective R' hsurj).comp eF.symm.surjective
  have hGH : G ∘ₗ H = (algebraMap R R' ϖ ^ e) • LinearMap.id := by
    have hφ : (algebraMap A R' (algebraMap R A ϖ ^ e)) = algebraMap R R' ϖ ^ e := by
      rw [map_pow]
      exact congrArg (· ^ e) (φ.commutes ϖ)
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [map_add, hx, hy, ← map_add]
    | tmul r ω =>
      have hω := LinearMap.congr_fun hh ω
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hω
      simp only [G, H, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.baseChange_tmul, hω, LinearMap.smul_apply, LinearMap.id_apply]
      rw [TensorProduct.tmul_smul, ← algebraMap_smul R' (algebraMap R A ϖ ^ e) (r ⊗ₜ[A] ω), hφ]
  have hc : algebraMap R R' ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ'.ne_zero
  have key := length_torsion_le_of_comp_eq_smul G H hG hc hGH
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ'.ne_zero), Ring.ord_of_irreducible hϖ']
    at key
  have : pointDefect φ = Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R])) := rfl
  rw [this]
  refine key.trans (le_of_eq ?_)
  simp

end Langlands.AlgebraicGeometry.DvrSmoothening
