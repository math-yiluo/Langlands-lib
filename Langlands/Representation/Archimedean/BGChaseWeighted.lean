import Langlands.Representation.Archimedean.BGChaseConclusion
import Langlands.Representation.Archimedean.LowerVermaKostant
import Langlands.Representation.Archimedean.LowerVermaDuflo
import Langlands.Representation.Archimedean.LowerVermaHomBound
import Langlands.Representation.Archimedean.LowerVermaProjective

/-!
# The Bernstein–Gelfand chase at a prescribed weight

A variant of `BGChase.complexJacquetBimodule_of_inputs` in which the weight `λ` of the lower
Verma module is prescribed instead of produced by Harish-Chandra's theorem: if `λ` is
`Z`-extremal and `M⁻(λ)` has the central character of the right action `ρ(u) = Λ_ℓ(uᵗ)`, then
`V` is not spanned by the vectors `ℓ(E_pq) v` (`p < q`) together with the vectors
`ℓ(E_pp) v - λ_p v`. The proof is the chase of `BGChaseConclusion` with the extra generators
`e ⊗ u (E_pp - λ_p)` of the kernel of `c_gen`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.BGChase

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping VermaGL

universe uV

variable {n : ℕ}

local notation "gl" => Matrix (Fin n) (Fin n) ℂ
local notation "U" => UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)

/-- The subspace of `V` spanned by the vectors `ℓ(E_pq) v` (`p < q`) and `ℓ(E_pp) v - λ_p v`. -/
def wtSpan {V : Type uV} [AddCommGroup V] [Module ℂ V] (ℓ : gl →ₗ⁅ℂ⁆ Module.End ℂ V)
    (lam : Fin n → ℂ) : Submodule ℂ V :=
  Submodule.span ℂ ({w | ∃ (p q : Fin n) (v : V), p < q ∧ ℓ (Matrix.single p q 1) v = w} ∪
    {w | ∃ (p : Fin n) (v : V), ℓ (Matrix.single p p 1) v - lam p • v = w})

namespace BData

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (D : BData n V) (lam : Fin n → ℂ)

theorem cM_gen_rmul_diag (p : Fin n) (x : D.E ⊗[ℂ] U) :
    cM lam (gen n lam) (D.rmul (unitU n p p - algebraMap ℂ U (lam p)) x) = 0 := by
  rw [rmul_eq_rmulE, cM_rmulE, sub_smul, unitU_smul_gen_diag, algebraMap_smul, sub_self,
    map_zero, LinearMap.zero_apply]

theorem ℓ_pmap_sub (p : Fin n) (x : D.E ⊗[ℂ] U) :
    D.ℓ (Matrix.single p p 1) (D.pmap x) - lam p • D.pmap x =
      D.pmap (D.rmul (unitU n p p - algebraMap ℂ U (lam p)) x) := by
  rw [pmap_rmul, map_sub, rhoR_ι, rhoR_algebraMap, Matrix.transpose_single, LinearMap.sub_apply,
    Module.algebraMap_end_apply]

/-- If `V` is spanned by the vectors `ℓ(E_pq) v` (`p < q`) and `ℓ(E_pp) v - λ_p v`, then for each
`e ∈ E` some `k` in the kernel of `p` satisfies `c_gen(k) = e ⊗ gen`. -/
theorem exists_ker_cM_gen_wt
    (hgen : ∀ S : Submodule ℂ V, D.E ≤ S → (∀ X, ∀ s ∈ S, D.ℓ X s ∈ S) → S = ⊤)
    (hspan : wtSpan D.ℓ lam = ⊤) (e : D.E) :
    ∃ k ∈ LinearMap.ker D.pmap, cM lam (gen n lam) k = e ⊗ₜ[ℂ] gen n lam := by
  let T : Submodule ℂ (D.E ⊗[ℂ] U) :=
    Submodule.span ℂ ({x | ∃ (a b : Fin n) (y : D.E ⊗[ℂ] U), b < a ∧ x = D.rmul (unitU n a b) y} ∪
      {x | ∃ (p : Fin n) (y : D.E ⊗[ℂ] U),
        x = D.rmul (unitU n p p - algebraMap ℂ U (lam p)) y})
  have hsurj : ∀ v : V, ∃ x, D.pmap x = v := fun v => by
    have hv : v ∈ LinearMap.range D.pmap := by rw [D.range_pmap hgen]; exact Submodule.mem_top
    exact hv
  have hT : (⊤ : Submodule ℂ V) ≤ T.map D.pmap := by
    rw [← hspan, wtSpan, Submodule.span_le]
    rintro _ (⟨p, q, v, hpq, rfl⟩ | ⟨p, v, rfl⟩)
    · obtain ⟨x, rfl⟩ := hsurj v
      refine ⟨D.rmul (unitU n q p) x, Submodule.subset_span (Or.inl ⟨q, p, x, hpq, rfl⟩), ?_⟩
      rw [ℓ_pmap, Matrix.transpose_single]
    · obtain ⟨x, rfl⟩ := hsurj v
      exact ⟨_, Submodule.subset_span (Or.inr ⟨p, x, rfl⟩), (D.ℓ_pmap_sub lam p x).symm⟩
  obtain ⟨y, hyT, hy⟩ := hT (Submodule.mem_top : (e : V) ∈ ⊤)
  have hcy : cM lam (gen n lam) y = 0 := by
    have hle : T ≤ LinearMap.ker (cM (E := D.E) lam (gen n lam)) := by
      rw [Submodule.span_le]
      rintro _ (⟨a, b, z, hab, rfl⟩ | ⟨p, z, rfl⟩)
      · exact D.cM_gen_rmul_of_lt lam hab z
      · exact D.cM_gen_rmul_diag lam p z
    exact hle hyT
  refine ⟨e ⊗ₜ[ℂ] 1 - y, ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, pmap_tmul_one, hy, sub_self]
  · rw [map_sub, hcy, sub_zero, cM_tmul, one_smul]

end BData

/-- **The Bernstein–Gelfand chase at a prescribed weight.** Let `ℓ`, `r` be commuting actions of
`𝔤𝔩_n(ℂ)` on `V` and `E ⊆ V` a nonzero finite-dimensional subspace, stable under
`ℓ(Y) - r(Yᵀ)`, spanned by vectors of integral weight for `ℓ(E_pp) - r(E_pp)` and generating `V`
under `ℓ`. Let `λ` be `Z`-extremal and `χ` a character of the center with
`ρ(z) = Λ_ℓ(zᵗ) = χ(z)` on `V` and `z • gen λ = χ(z) gen λ`. Then the vectors `ℓ(E_pq) v`
(`p < q`) and `ℓ(E_pp) v - λ_p v` do not span `V`. -/
theorem wtSpan_ne_top {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ℓ r : gl →ₗ⁅ℂ⁆ Module.End ℂ V) (hcomm : ∀ X Y, ℓ X * r Y = r Y * ℓ X)
    (E : Submodule ℂ V) (hEfd : FiniteDimensional ℂ E) (hE0 : E ≠ ⊥)
    (hstable : ∀ Y : gl, ∀ e ∈ E, ℓ Y e - r Y.transpose e ∈ E)
    (hW : E ≤ Submodule.span ℂ {e | e ∈ E ∧ ∃ m : Fin n → ℤ, ∀ p : Fin n,
        ℓ (Matrix.single p p 1) e - r (Matrix.single p p 1) e = (m p : ℂ) • e})
    (hgen : ∀ S : Submodule ℂ V, E ≤ S → (∀ X, ∀ s ∈ S, ℓ X s ∈ S) → S = ⊤)
    (lam : Fin n → ℂ) (hlam : IsZExtremal n lam) (χ : center n →ₐ[ℂ] ℂ)
    (hχR : ∀ z : center n, rhoR ℓ z = algebraMap ℂ (Module.End ℂ V) (χ z))
    (hχ : ∀ z : center n, (z : glU n) • gen n lam = χ z • gen n lam) :
    wtSpan ℓ lam ≠ ⊤ := by
  intro hspan
  let D : BData n V := ⟨ℓ, r, hcomm, E, hstable⟩
  have hDfd : FiniteDimensional ℂ D.E := hEfd
  obtain ⟨b, hbE, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
  have hkE : HasIntegralWeights D.kE := D.intSpan_kE hW
  have hWt := VermaPBW.lowerVermaWeight
  have hDuflo := VermaPBW.lowerVermaDuflo
  have hzero : ∀ e : D.E, (e : V) = 0 := by
    intro e
    obtain ⟨h, hh, hcm⟩ := exists_mem_cM_eq D.kE lam hWt hDuflo VermaKostant.lowerVermaKostant
      VermaPBW.lowerVermaHomBound VermaPBW.lowerVermaProjective hlam χ hχ hkE
      (LinearMap.ker D.pmap) (fun _ _ hx => D.rmul_mem_ker hx) (fun Y _ hx => D.adP_mem_ker Y hx)
      (D.exists_ker_cM_gen_wt lam hgen hspan) e
    have hx := D.pmap_eq_zero_of_cM lam hWt hDuflo χ hχR hχ (h - e ⊗ₜ[ℂ] 1) fun m => by
      rw [map_sub, hcm m, cM_tmul, one_smul, sub_self]
    rw [map_sub, LinearMap.mem_ker.1 hh, BData.pmap_tmul_one, zero_sub, neg_eq_zero] at hx
    exact hx
  exact hb0 (by simpa using hzero ⟨b, hbE⟩)

end Langlands.Archimedean.BGChase
