import Langlands.Representation.Archimedean.BGChaseCore
import Langlands.Representation.Archimedean.ComplexJacquetBimodule

/-!
# The Bernstein–Gelfand chase: conclusion

Under the hypotheses of the bimodule statement, assume that the strictly upper triangular
matrix units span `V` under `ℓ`. Then every `e ⊗ gen` (`gen` the generator of a lower Verma
module `M⁻(λ)`) is `c_gen(k)` for some `k` in the kernel `K` of `p : E ⊗ U → V`, and a degree
truncation of `K` is a finite-dimensional `ad`-stable subspace `F` with the same property. The
abstract core then gives, for each `e ∈ E`, an element `h ∈ K` acting on `M⁻(λ)` like `e ⊗ 1`;
Duflo's theorem forces `e = p(e ⊗ 1) - p(h) = 0` (Bernstein–Gelfand 1980, proof of Theorem 5.9
in 5.10).

The steps involving `F` are stated for an abstract type `E` (rather than the subspace `E ⊆ V`),
which keeps instance synthesis on subspaces of `E ⊗ U` and their endomorphisms working.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.BGChase

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping VermaGL

universe uE uV

variable {n : ℕ}

local notation "gl" => Matrix (Fin n) (Fin n) ℂ
local notation "U" => UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)

/-! ## Degree truncations of `E ⊗ U` and the subspace `F` -/

section Truncation

-- The local notations are not used inside `variable`: there they lose the binding of `n`.
variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- The truncation `E ⊗ U_d` of `E ⊗ U`. -/
def truncE (E : Type uE) [AddCommGroup E] [Module ℂ E] (d : ℕ) : Submodule ℂ (E ⊗[ℂ] U) :=
  LinearMap.range (LinearMap.lTensor E (degreeFiltration ℂ gl d).subtype)

theorem truncE_mono {d d' : ℕ} (h : d ≤ d') : truncE (n := n) E d ≤ truncE E d' := by
  rintro _ ⟨y, rfl⟩
  refine ⟨LinearMap.lTensor E (Submodule.inclusion (degreeFiltration_mono ℂ gl h)) y, ?_⟩
  rw [← LinearMap.lTensor_comp_apply]
  rfl

theorem exists_mem_truncE (x : E ⊗[ℂ] U) : ∃ d, x ∈ truncE E d := by
  induction x with
  | tmul e u =>
    obtain ⟨d, hd⟩ := exists_mem_degreeFiltration ℂ gl u
    exact ⟨d, e ⊗ₜ[ℂ] ⟨u, hd⟩, rfl⟩
  | add a b ha hb =>
    obtain ⟨d₁, h₁⟩ := ha
    obtain ⟨d₂, h₂⟩ := hb
    exact ⟨max d₁ d₂, Submodule.add_mem _ (truncE_mono (le_max_left _ _) h₁)
      (truncE_mono (le_max_right _ _) h₂)⟩

theorem tensorLie_mem_truncE (kE : gl →ₗ⁅ℂ⁆ Module.End ℂ E) (Y : gl) {d : ℕ} {x : E ⊗[ℂ] U}
    (hx : x ∈ truncE E d) : tensorLie kE adU Y x ∈ truncE E d := by
  obtain ⟨y, rfl⟩ := hx
  let a : Module.End ℂ (degreeFiltration ℂ gl d) :=
    (adU Y).restrict fun _ hu => adU_mem_degreeFiltration Y hu
  refine ⟨LinearMap.rTensor _ (kE Y) y + LinearMap.lTensor E a y, ?_⟩
  induction y with
  | tmul e u => rfl
  | add y₁ y₂ h₁ h₂ => simp only [map_add] at h₁ h₂ ⊢; rw [← h₁, ← h₂]; abel

instance [FiniteDimensional ℂ E] (d : ℕ) : FiniteDimensional ℂ (truncE (n := n) E d) :=
  LinearMap.finiteDimensional_range _

/-- If every `e ⊗ gen` is `c_gen(k)` for some `k` in an `ad`-stable subspace `K`, then `K`
contains a finite-dimensional `ad`-stable subspace `F` with the same property. -/
theorem exists_F (kE : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ E) (lam : Fin n → ℂ)
    [FiniteDimensional ℂ E] (K : Submodule ℂ (E ⊗[ℂ] U))
    (hKad : ∀ Y, ∀ x ∈ K, tensorLie kE adU Y x ∈ K)
    (hk : ∀ e : E, ∃ k ∈ K, cM lam (gen n lam) k = e ⊗ₜ[ℂ] gen n lam) :
    ∃ F : Submodule ℂ (E ⊗[ℂ] U), F ≤ K ∧ FiniteDimensional ℂ F ∧
      (∀ Y, ∀ x ∈ F, tensorLie kE adU Y x ∈ F) ∧
      ∀ e : E, ∃ x ∈ F, cM lam (gen n lam) x = e ⊗ₜ[ℂ] gen n lam := by
  let bE := Module.finBasis ℂ E
  choose k hkK hkc using hk
  choose d hd using fun j => exists_mem_truncE (n := n) (k (bE j))
  let d0 := Finset.univ.sup d
  refine ⟨K ⊓ truncE E d0, inf_le_left, ?_, ?_, ?_⟩
  · exact Submodule.finiteDimensional_of_le inf_le_right
  · intro Y x hx
    exact ⟨hKad Y x hx.1, tensorLie_mem_truncE kE Y hx.2⟩
  · intro e
    refine ⟨∑ j, bE.repr e j • k (bE j), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      ⟨hkK _, truncE_mono (Finset.le_sup (Finset.mem_univ j)) (hd j)⟩, ?_⟩
    rw [map_sum]
    simp only [map_smul, hkc]
    conv_rhs => rw [← bE.sum_repr e]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul' _ _ _

/-- Bernstein–Gelfand 1980, proof of 5.10: if `K ⊆ E ⊗ U` is stable under right multiplication
and `ad`, and every `e ⊗ gen` is `c_gen(k)` for some `k ∈ K`, then for every `e ∈ E` some
`h ∈ K` satisfies `c_m(h) = e ⊗ m` for all `m ∈ M⁻(λ)`. -/
theorem exists_mem_cM_eq (kE : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ E) (lam : Fin n → ℂ)
    (hWt : LowerVermaWeightStatement) (hDuflo : LowerVermaDufloStatement)
    (hK : KostantMultiplicityStatement.{uE}) (hB : LowerVermaHomBoundStatement.{uE})
    (hP : LowerVermaProjectiveStatement.{uE, uE}) (hlam : IsZExtremal n lam)
    (χ : center n →ₐ[ℂ] ℂ) (hχ : ∀ z : center n, (z : glU n) • gen n lam = χ z • gen n lam)
    [FiniteDimensional ℂ E] (hkE : HasIntegralWeights kE) (K : Submodule ℂ (E ⊗[ℂ] U))
    (hKr : ∀ u, ∀ x ∈ K, rmulE u x ∈ K) (hKad : ∀ Y, ∀ x ∈ K, tensorLie kE adU Y x ∈ K)
    (hk : ∀ e : E, ∃ k ∈ K, cM lam (gen n lam) k = e ⊗ₜ[ℂ] gen n lam) (e : E) :
    ∃ h ∈ K, ∀ m : LowerVerma n lam, cM lam m h = e ⊗ₜ[ℂ] m := by
  obtain ⟨F, hFK, hFfd, hFad, hFgen⟩ := exists_F kE lam K hKad hk
  have hsF : HasIntegralWeights (restrictLie (tensorLie kE adU) F hFad) :=
    intSpan_restrictLie_of_le F hFad
      (by rw [intSpan_tensorLie (σ := kE) (τ := adU) hkE intSpan_adU]; exact le_top)
  have hFgen' : ∀ e : E, ∃ x : F, cM lam (gen n lam) (F.subtype x) = e ⊗ₜ[ℂ] gen n lam := by
    intro e
    obtain ⟨x, hx, hcx⟩ := hFgen e
    exact ⟨⟨x, hx⟩, hcx⟩
  obtain ⟨h, hh, hcm⟩ := exists_h kE lam (restrictLie (tensorLie kE adU) F hFad) F.subtype
    (fun _ _ => rfl) hWt hDuflo hK hB hP hlam χ hχ hkE hsF hFgen' e
  refine ⟨h, Submodule.span_le.2 ?_ hh, hcm⟩
  rintro _ ⟨u, x, rfl⟩
  exact hKr u _ (hFK x.2)

end Truncation

/-! ## The bimodule data -/

namespace BData

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (D : BData n V) (lam : Fin n → ℂ)

theorem rmul_eq_rmulE (u : U) (x : D.E ⊗[ℂ] U) : D.rmul u x = rmulE u x := rfl

theorem cM_gen_rmul_of_lt {a b : Fin n} (h : b < a) (x : D.E ⊗[ℂ] U) :
    cM lam (gen n lam) (D.rmul (unitU n a b) x) = 0 := by
  rw [rmul_eq_rmulE, cM_rmulE, unitU_smul_gen_of_lt lam h, map_zero, LinearMap.zero_apply]

/-- If the strictly upper triangular matrix units span `V` under `ℓ`, then for each `e ∈ E` some
`k` in the kernel of `p` satisfies `c_gen(k) = e ⊗ gen`. -/
theorem exists_ker_cM_gen
    (hgen : ∀ S : Submodule ℂ V, D.E ≤ S → (∀ X, ∀ s ∈ S, D.ℓ X s ∈ S) → S = ⊤)
    (hspan : Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), p < q ∧ D.ℓ (Matrix.single p q 1) v = w}
      = ⊤) (e : D.E) :
    ∃ k ∈ LinearMap.ker D.pmap, cM lam (gen n lam) k = e ⊗ₜ[ℂ] gen n lam := by
  let T : Submodule ℂ (D.E ⊗[ℂ] U) :=
    Submodule.span ℂ {x | ∃ (a b : Fin n) (y : D.E ⊗[ℂ] U), b < a ∧ x = D.rmul (unitU n a b) y}
  have hT : (⊤ : Submodule ℂ V) ≤ T.map D.pmap := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨p, q, v, hpq, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x, D.pmap x = v := by
      have hv : v ∈ LinearMap.range D.pmap := by rw [D.range_pmap hgen]; exact Submodule.mem_top
      exact hv
    refine ⟨D.rmul (unitU n q p) x, Submodule.subset_span ⟨q, p, x, hpq, rfl⟩, ?_⟩
    rw [ℓ_pmap, Matrix.transpose_single]
  obtain ⟨y, hyT, hy⟩ := hT (Submodule.mem_top : (e : V) ∈ ⊤)
  have hcy : cM lam (gen n lam) y = 0 := by
    have hle : T ≤ LinearMap.ker (cM (E := D.E) lam (gen n lam)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, b, z, hab, rfl⟩
      exact D.cM_gen_rmul_of_lt lam hab z
    exact hle hyT
  refine ⟨e ⊗ₜ[ℂ] 1 - y, ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, pmap_tmul_one, hy, sub_self]
  · rw [map_sub, hcy, sub_zero, cM_tmul, one_smul]

/-- An element of `E ⊗ U` acting by zero on `M⁻(λ)` (through `c_m`) is killed by `p`, when `λ`
has the central character of the right action (Duflo's theorem). -/
theorem pmap_eq_zero_of_cM (hWt : LowerVermaWeightStatement) (hDuflo : LowerVermaDufloStatement)
    [FiniteDimensional ℂ D.E] (χ : center n →ₐ[ℂ] ℂ)
    (hχR : ∀ z : center n, rhoR D.ℓ z = algebraMap ℂ (Module.End ℂ V) (χ z))
    (hχ : ∀ z : center n, (z : glU n) • gen n lam = χ z • gen n lam) (x : D.E ⊗[ℂ] U)
    (hx : ∀ m : LowerVerma n lam, cM lam m x = 0) : D.pmap x = 0 := by
  let bE := Module.finBasis ℂ D.E
  rw [D.pmap_eq_sum bE x]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hact : envelopingAction (action n lam)
      (TensorProduct.lid ℂ U (LinearMap.rTensor U (bE.coord i) x)) = 0 := by
    refine LinearMap.ext fun m => ?_
    rw [envelopingAction_action, LinearMap.zero_apply, ← evalBil_apply,
      ← lid_rTensor_lTensor, ← cM_apply, hx m, map_zero, map_zero]
  have hmem := mem_span_of_action_eq_zero hWt hDuflo χ hχ hact
  rw [D.rhoR_eq_zero_of_mem_span χ hχR hmem, LinearMap.zero_apply]

end BData

/-- The Bernstein–Gelfand inputs imply one-sided nonvanishing for Harish-Chandra bimodules of
`𝔤𝔩_n(ℂ)` (Bernstein–Gelfand 1980, Theorem 5.9, proof in 5.10). -/
theorem complexJacquetBimodule_of_inputs (hWt : LowerVermaWeightStatement)
    (hDuflo : LowerVermaDufloStatement) (hK : KostantMultiplicityStatement.{uV})
    (hCC : CentralCharacterStatement) (hB : LowerVermaHomBoundStatement.{uV})
    (hP : LowerVermaProjectiveStatement.{uV, uV}) : ComplexJacquetBimoduleStatement.{uV} := by
  intro n V _ _ ℓ r hcomm E hEfd hE0 hstable hW hgen hInf hspan
  let D : BData n V := ⟨ℓ, r, hcomm, E, hstable⟩
  have hDfd : FiniteDimensional ℂ D.E := hEfd
  obtain ⟨b, hbE, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
  have : Nontrivial V := nontrivial_of_ne b 0 hb0
  obtain ⟨χ, hχR⟩ := exists_rhoR_character D.ℓ hInf
  obtain ⟨lam, hlam, hχ⟩ := hCC n χ
  have hkE : HasIntegralWeights D.kE := D.intSpan_kE hW
  have hzero : ∀ e : D.E, (e : V) = 0 := by
    intro e
    obtain ⟨h, hh, hcm⟩ := exists_mem_cM_eq D.kE lam hWt hDuflo hK hB hP hlam χ hχ hkE
      (LinearMap.ker D.pmap) (fun _ _ hx => D.rmul_mem_ker hx) (fun Y _ hx => D.adP_mem_ker Y hx)
      (D.exists_ker_cM_gen lam hgen hspan) e
    have hx := D.pmap_eq_zero_of_cM lam hWt hDuflo χ hχR hχ (h - e ⊗ₜ[ℂ] 1) fun m => by
      rw [map_sub, hcm m, cM_tmul, one_smul, sub_self]
    rw [map_sub, LinearMap.mem_ker.1 hh, BData.pmap_tmul_one, zero_sub, neg_eq_zero] at hx
    exact hx
  exact hb0 (by simpa using hzero ⟨b, hbE⟩)

end Langlands.Archimedean.BGChase
