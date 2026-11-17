import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction
import Langlands.Representation.Archimedean.RealInductionStagesFourier
import Langlands.Representation.Archimedean.RealInductionStagesSlice
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.PartialJacquetIntegral
import Langlands.Representation.Archimedean.JacquetKernel
import Langlands.Representation.KFiniteDual

/-!
# Injective swaps of adjacent blocks are surjective

This file proves `RealSwapInjectiveIntertwinerSurjectiveStatement`: every injective
`(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
`pre ++ x :: y :: post` to those of `pre ++ y :: x :: post` is surjective.

The proof counts dimensions of spaces of `O(n)`-intertwiners, without a decomposition into
`O(n)`-types.

* `surjective_of_injective`: let `T : V → W` and `Φ : W → V` be injective `K`-intertwiners
  between admissible representations, every vector of `W` being `K`-finite with continuous
  coefficients. For `w ∈ W` let `S` be the span of the orbit of `w`, with matrices `τ` in a
  basis. Composition with `T` and with `Φ` are injective maps between the finite-dimensional
  spaces of `K`-intertwiners from `τ` into `V` and into `W`, so these spaces have equal
  dimension and composition with `T` is bijective. The inclusion of `S` is therefore `T ∘ A`,
  and `w` lies in the range of `T`.
* `exists_perm_injection`: for a permutation `τ` of the positions that carries the position
  characters and the induction blocks of `ds'` to those of `ds`, `f ↦ (κ ↦ f(P_τ κ))` on
  `O(n)`, extended to `GL_n(ℝ)` by `PrincipalSeriesExtension.extension`, is an injective
  `O(n)`-intertwiner from the `O(n)`-finite functions of the standard module of `ds'` to
  those of `ds`. Here `(P_τ κ)_{ij} = κ_{τ(i), j}`.
* `swapPerm`: the permutation exchanging the positions of two adjacent blocks.
-/

noncomputable section

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

namespace RealSwapSurjective

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

/-! ## Injective intertwiners in both directions -/

section Abstract

universe uK uV uW

variable {K : Type uK} [Group K] [TopologicalSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ K V} {σ : Representation ℂ K W}

/-- Composition with a `K`-intertwiner `T`, on the `K`-intertwiners from a matrix
representation `τ`. -/
def postComp (T : V →ₗ[ℂ] W) (hT : ∀ (k : K) (v : V), T (ρ k v) = σ k (T v)) (d : ℕ)
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners ρ d τ →ₗ[ℂ] gkIntertwiners σ d τ where
  toFun A := ⟨T ∘ₗ (A : (Fin d → ℂ) →ₗ[ℂ] V), fun k x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, A.2 k x, hT]⟩
  map_add' A B := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp
  map_smul' c A := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp

omit [TopologicalSpace K] in
theorem postComp_apply (T : V →ₗ[ℂ] W) (hT : ∀ (k : K) (v : V), T (ρ k v) = σ k (T v))
    (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ) (A : gkIntertwiners ρ d τ) (x : Fin d → ℂ) :
    ((postComp T hT d τ A : gkIntertwiners σ d τ) : (Fin d → ℂ) →ₗ[ℂ] W) x =
      T ((A : (Fin d → ℂ) →ₗ[ℂ] V) x) :=
  rfl

omit [TopologicalSpace K] in
theorem postComp_injective (T : V →ₗ[ℂ] W) (hT : ∀ (k : K) (v : V), T (ρ k v) = σ k (T v))
    (hTi : Function.Injective T) (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    Function.Injective (postComp T hT d τ) := by
  intro A B h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply hTi
  rw [← postComp_apply T hT d τ A x, ← postComp_apply T hT d τ B x, h]

/-- **Dimension count.** An injective `K`-intertwiner `T : V → W` between admissible
representations is surjective when there is an injective `K`-intertwiner `Φ : W → V` and
every vector of `W` is `K`-finite with continuous coefficients. -/
theorem surjective_of_injective (hV : IsAdmissibleGKModule ρ) (hW : IsAdmissibleGKModule σ)
    (hfin : ∀ w : W, FiniteVectors.IsFiniteVector σ w)
    (hcont : ∀ (w : W) (ℓ : W →ₗ[ℂ] ℂ), Continuous fun k => ℓ (σ k w))
    (T : V →ₗ[ℂ] W) (hT : ∀ (k : K) (v : V), T (ρ k v) = σ k (T v))
    (hTi : Function.Injective T)
    (Φ : W →ₗ[ℂ] V) (hΦ : ∀ (k : K) (w : W), Φ (σ k w) = ρ k (Φ w))
    (hΦi : Function.Injective Φ) : Function.Surjective T := by
  intro w
  let S := FiniteVectors.orbitSubrepresentation σ w
  have : FiniteDimensional ℂ S.toSubmodule := hfin w
  let τ := KFiniteDual.subMatrix S
  have hτ : Continuous τ := KFiniteDual.continuous_subMatrix hcont S
  have : FiniteDimensional ℂ (gkIntertwiners ρ _ τ) := hV _ τ hτ
  have : FiniteDimensional ℂ (gkIntertwiners σ _ τ) := hW _ τ hτ
  let b := Module.finBasis ℂ S.toSubmodule
  let ι : (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) →ₗ[ℂ] W :=
    S.toSubmodule.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hι : ι ∈ gkIntertwiners σ _ τ := by
    intro k x
    have h := KFiniteDual.equivFun_symm_coordRep S k x
    rw [KFiniteDual.coordRep_apply] at h
    change ((b.equivFun.symm (τ k *ᵥ x) : S.toSubmodule) : W) =
      σ k ((b.equivFun.symm x : S.toSubmodule) : W)
    rw [h]
    rfl
  have h1 := LinearMap.finrank_le_finrank_of_injective (postComp_injective T hT hTi _ τ)
  have h2 := LinearMap.finrank_le_finrank_of_injective (postComp_injective Φ hΦ hΦi _ τ)
  have hs : Function.Surjective (postComp T hT _ τ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm h1 h2)).mp
      (postComp_injective T hT hTi _ τ)
  obtain ⟨A, hA⟩ := hs ⟨ι, hι⟩
  let x := b.equivFun ⟨w, FiniteVectors.self_mem_orbitSpan σ w⟩
  refine ⟨(A : (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) →ₗ[ℂ] V) x, ?_⟩
  rw [← postComp_apply T hT _ τ A x, hA]
  show ((b.equivFun.symm (b.equivFun ⟨w, FiniteVectors.self_mem_orbitSpan σ w⟩) :
    S.toSubmodule) : W) = w
  rw [LinearEquiv.symm_apply_apply]

end Abstract

/-! ## Permutation matrices -/

section Permutation

variable {n : ℕ}

/-- The permutation matrix `P_τ`, with `(P_τ M)_{ij} = M_{τ(i), j}`. -/
def permMat (τ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ).submatrix τ id

theorem permMat_mul (τ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℝ) :
    permMat τ * M = M.submatrix τ id := by
  ext i j
  simp [permMat, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]

/-- `P_τ M = N P_τ` when `M_{τ(i), τ(l)} = N_{i, l}`. -/
theorem permMat_mul_eq (τ : Equiv.Perm (Fin n)) {M N : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i l, M (τ i) (τ l) = N i l) : permMat τ * M = N * permMat τ := by
  rw [permMat_mul]
  ext i j
  have hj : ∀ k : Fin n, (τ k = j) ↔ (k = τ.symm j) := fun k => (Equiv.eq_symm_apply τ).symm
  simp [Matrix.mul_apply, permMat, Matrix.one_apply, hj]
  rw [← h]
  simp

theorem permMat_mem_unitaryGroup (τ : Equiv.Perm (Fin n)) :
    permMat τ ∈ Matrix.unitaryGroup (Fin n) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, permMat_mul]
  ext i j
  by_cases h : i = j
  · subst h
    simp [permMat, Matrix.one_apply]
  · simp [permMat, h, τ.injective.eq_iff]

/-- `P_τ` as an element of `O(n)`. -/
def permU (τ : Equiv.Perm (Fin n)) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨permMat τ, permMat_mem_unitaryGroup τ⟩

theorem permU_val (τ : Equiv.Perm (Fin n)) :
    ((permU τ : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = permMat τ :=
  rfl

/-- `P_τ diag(sgn a) = diag(sgn (a ∘ τ)) P_τ`. -/
theorem permU_mul_signDiagonal (τ : Equiv.Perm (Fin n)) (a : Fin n → ℝ) :
    permU τ * PrincipalSeriesExtension.signDiagonal a =
      PrincipalSeriesExtension.signDiagonal (fun i => a (τ i)) * permU τ := by
  apply Subtype.ext
  change permMat τ * Matrix.diagonal (fun i => GramFormula.signReal (a i)) =
    Matrix.diagonal (fun i => GramFormula.signReal (a (τ i))) * permMat τ
  refine permMat_mul_eq τ fun i l => ?_
  simp only [Matrix.diagonal_apply, τ.injective.eq_iff]

/-- `P_τ r_p(θ) = r_{p'}(θ) P_τ` when `τ` carries `p', p' + 1` to `p, p + 1`. -/
theorem permMat_mul_blockRotation (τ : Equiv.Perm (Fin n)) {p p' : ℕ} (hp : p + 1 < n)
    (hp' : p' + 1 < n)
    (hτ : ∀ i : Fin n, ((i : ℕ) = p' → (τ i : ℕ) = p) ∧ ((i : ℕ) = p' + 1 → (τ i : ℕ) = p + 1))
    (θ : ℝ) :
    permMat τ * (blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) =
      (blockRotation n p' θ : Matrix (Fin n) (Fin n) ℝ) * permMat τ := by
  have e1 : ∀ i : Fin n, (τ i : ℕ) = p ↔ (i : ℕ) = p' := by
    intro i
    refine ⟨fun h => ?_, (hτ i).1⟩
    have h' := (hτ ⟨p', by omega⟩).1 rfl
    have : τ i = τ ⟨p', by omega⟩ := Fin.ext (by rw [h, h'])
    exact congrArg Fin.val (τ.injective this)
  have e2 : ∀ i : Fin n, (τ i : ℕ) = p + 1 ↔ (i : ℕ) = p' + 1 := by
    intro i
    refine ⟨fun h => ?_, (hτ i).2⟩
    have h' := (hτ ⟨p' + 1, hp'⟩).2 rfl
    have : τ i = τ ⟨p' + 1, hp'⟩ := Fin.ext (by rw [h, h'])
    exact congrArg Fin.val (τ.injective this)
  refine permMat_mul_eq τ fun i l => ?_
  rw [RealBlockRotation.blockRotation_apply hp, RealBlockRotation.blockRotation_apply hp']
  simp only [e1, e2, τ.injective.eq_iff]

end Permutation

/-! ## Pulling back along a permutation of the positions -/

section Pull

variable {n : ℕ}

theorem continuous_toUnits :
    Continuous (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ → Langlands.GeneralLinear n ℝ) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩

/-- `f ↦ (κ ↦ f(P_τ κ))`, from functions on `GL_n(ℝ)` to functions on `O(n)`. -/
def pull (τ : Equiv.Perm (Fin n)) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℝ → ℂ) where
  toFun f κ := f (Unitary.toUnits (permU τ * κ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_apply (τ : Equiv.Perm (Fin n)) (f : Langlands.GeneralLinear n ℝ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) : pull τ f κ = f (Unitary.toUnits (permU τ * κ)) :=
  rfl

variable {ds ds' : List RealBlock} {τ : Equiv.Perm (Fin n)}

theorem continuous_pull {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) :
    Continuous (pull τ f) :=
  hf.comp (continuous_toUnits.comp (continuous_const.mul continuous_id))

theorem pull_rightTranslation (f : Langlands.GeneralLinear n ℝ → ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    pull τ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (Unitary.toUnits k) f) =
      fun κ => pull τ f (κ * k) := by
  funext κ
  change f (Unitary.toUnits (permU τ * κ) * Unitary.toUnits k) =
    f (Unitary.toUnits (permU τ * (κ * k)))
  rw [← map_mul, mul_assoc]

theorem finiteDimensional_pull {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => pull τ f (x * k))) := by
  rw [mem_kFiniteVectors_iff] at hf
  have hle : Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => pull τ f (x * k)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) f)).map (pull τ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, ?_⟩
    exact pull_rightTranslation f k
  exact Submodule.finiteDimensional_of_le hle

/-- The value of a principal-series character at signs is the product of the characters at
the signs. -/
theorem principalSeriesCharacter_signUnit_perm (hχ : ∀ i : Fin n,
      realPositionCharacter ds' i = realPositionCharacter ds (τ i)) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds') (fun i => GramFormula.signUnit (a (τ i))) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds)
        (fun i => GramFormula.signUnit (a i)) := by
  rw [JacquetKernel.principalSeriesCharacter_sign n (fun i => a (τ i)),
    JacquetKernel.principalSeriesCharacter_sign n a]
  simp only [hχ]
  exact Equiv.prod_comp τ (fun i => realPositionCharacter ds i (GramFormula.signUnit (a i)))

theorem pull_signDiagonal (hχ : ∀ i : Fin n,
      realPositionCharacter ds' i = realPositionCharacter ds (τ i))
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n (realPositionCharacter ds'))
    (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    pull τ f (PrincipalSeriesExtension.signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => GramFormula.signUnit (a i)) *
        pull τ f κ := by
  rw [pull_apply, ← mul_assoc, permU_mul_signDiagonal, mul_assoc,
    PartialJacquet.signDiagonal_toUnits (fun i => a (τ i)), hf.2,
    principalSeriesCharacter_signUnit_perm hχ, pull_apply]

end Pull

/-! ## The injection -/

section Injection

variable {n : ℕ} {ds ds' : List RealBlock} {τ : Equiv.Perm (Fin n)}

open PrincipalSeriesExtension GramFormula

/-- The extension of `pull τ f`. -/
def extPull (ds : List RealBlock) (τ : Equiv.Perm (Fin n)) (f : Langlands.GeneralLinear n ℝ → ℂ) :
    Langlands.GeneralLinear n ℝ → ℂ :=
  extension (shiftedExponent n (realPositionExponent ds)) (pull τ f)

theorem extPull_unitary (f : Langlands.GeneralLinear n ℝ → ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    extPull ds τ f (Unitary.toUnits κ) = pull τ f κ :=
  extension_unitary _ _ κ

theorem extPull_mem_kFinite_principalSeries (hχ : ∀ i : Fin n,
      realPositionCharacter ds' i = realPositionCharacter ds (τ i))
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)) :
    extPull ds τ f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds))
      (unitaryCompact ℝ n) :=
  extension_mem_kFiniteFunctions (realPositionExponent ds)
    (realPositionCharacter_eq_signUnit_mul ds) (continuous_pull hf.1.1.1.continuous)
    (finiteDimensional_pull hf.2) (pull_signDiagonal hχ hf.1.1)

theorem extPull_mem (hN : realRank ds = n)
    (hχ : ∀ i : Fin n, realPositionCharacter ds' i = realPositionCharacter ds (τ i))
    (hblk : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∃ p' : ℕ, realInducedBlockAt ds' p' = some d ∧
        ∀ i : Fin n, ((i : ℕ) = p' → (τ i : ℕ) = p) ∧ ((i : ℕ) = p' + 1 → (τ i : ℕ) = p + 1))
    (hN' : realRank ds' = n)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)) :
    extPull ds τ f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) := by
  have h := extPull_mem_kFinite_principalSeries hχ hf
  refine ⟨InductionStages.mem_realStandardModule_of_unitaryCompact hN h.1 ?_, h.2⟩
  intro p d hd k hk κ hκ
  obtain ⟨p', hd', hτ⟩ := hblk p d hd
  have hp : p + 1 < n := hN ▸ realInducedBlockAt_lt hd
  have hp' : p' + 1 < n := hN' ▸ realInducedBlockAt_lt hd'
  let κ₀ : Matrix.unitaryGroup (Fin n) ℝ := ⟨(κ : Matrix (Fin n) (Fin n) ℝ), hκ⟩
  have hint : ∀ θ : ℝ, extPull ds τ f (blockRotation n p θ * κ) =
      f (blockRotation n p' θ * Unitary.toUnits (permU τ * κ₀)) := by
    intro θ
    have hmem : ((blockRotation n p θ * κ : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ :=
      (unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hκ
    have hg : blockRotation n p θ * κ = Unitary.toUnits (⟨_, hmem⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
    rw [hg, extPull_unitary, pull_apply]
    congr 1
    apply Units.ext
    change permMat τ * ((blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) *
      (κ : Matrix (Fin n) (Fin n) ℝ)) =
        (blockRotation n p' θ : Matrix (Fin n) (Fin n) ℝ) *
          (permMat τ * (κ : Matrix (Fin n) (Fin n) ℝ))
    rw [← mul_assoc, permMat_mul_blockRotation τ hp hp' hτ θ, mul_assoc]
  have hc := hf.1.2 p' d hd' k hk (Unitary.toUnits (permU τ * κ₀))
  unfold blockFourierCoefficient at hc ⊢
  simp only [hint]
  exact hc

/-- **The injection.** For a permutation `τ` carrying the position characters and the
induction blocks of `ds'` to those of `ds`, `f ↦ extension(κ ↦ f(P_τ κ))` is an injective
`O(n)`-intertwiner from the `O(n)`-finite functions of the standard module of `ds'` to those
of `ds`. -/
theorem exists_perm_injection (hN : realRank ds = n) (hN' : realRank ds' = n)
    (hχ : ∀ i : Fin n, realPositionCharacter ds' i = realPositionCharacter ds (τ i))
    (hblk : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∃ p' : ℕ, realInducedBlockAt ds' p' = some d ∧
        ∀ i : Fin n, ((i : ℕ) = p' → (τ i : ℕ) = p) ∧ ((i : ℕ) = p' + 1 → (τ i : ℕ) = p + 1)) :
    ∃ Φ : kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℝ)
          (f : kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)),
        Φ (realStandardRep n ds' k f) = realStandardRep n ds k (Φ f)) ∧
        Function.Injective Φ := by
  let Φ : kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) :=
    { toFun := fun f => ⟨extPull ds τ f, extPull_mem hN hχ hblk hN' f.2⟩
      map_add' := fun f g => by
        apply Subtype.ext
        change extension (shiftedExponent n (realPositionExponent ds))
            (pull τ ((f : Langlands.GeneralLinear n ℝ → ℂ) + g)) =
          extension (shiftedExponent n (realPositionExponent ds)) (pull τ f) +
            extension (shiftedExponent n (realPositionExponent ds)) (pull τ g)
        rw [map_add]
        exact (extensionLinear _).map_add _ _
      map_smul' := fun c f => by
        apply Subtype.ext
        change extension (shiftedExponent n (realPositionExponent ds))
            (pull τ (c • (f : Langlands.GeneralLinear n ℝ → ℂ))) =
          c • extension (shiftedExponent n (realPositionExponent ds)) (pull τ f)
        rw [map_smul]
        exact (extensionLinear _).map_smul _ _ }
  refine ⟨Φ, fun k f => ?_, ?_⟩
  · apply Subtype.ext
    change extPull ds τ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (Unitary.toUnits k) f) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (Unitary.toUnits k)
        (extPull ds τ f)
    have hf := f.2
    unfold extPull
    rw [rightTranslation_extension (realPositionExponent ds)
      (realPositionCharacter_eq_signUnit_mul ds) (continuous_pull hf.1.1.1.continuous)
      (finiteDimensional_pull hf.2) (pull_signDiagonal hχ hf.1.1) k, pull_rightTranslation]
  · rw [injective_iff_map_eq_zero]
    intro f hf0
    have hv : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ, pull τ f κ = 0 := by
      intro κ
      rw [← extPull_unitary (ds := ds)]
      have := congrArg (fun g : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =>
        (g : Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits κ)) hf0
      exact this
    apply Subtype.ext
    refine eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1 fun g hg => ?_
    have h := hv ((permU τ)⁻¹ * ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩)
    rw [pull_apply, ← mul_assoc, mul_inv_cancel, one_mul] at h
    have hg' : (Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ :
        Matrix.unitaryGroup (Fin n) ℝ)) = g := Units.ext rfl
    rw [hg'] at h
    exact h

end Injection

/-! ## Exchanging two adjacent blocks -/

section Swap

/-- The positions of `pre ++ y :: x :: post` mapped to those of `pre ++ x :: y :: post`, for
`P = rank pre`, `a = rank x`, `b = rank y`. -/
def swapIdx (P a b i : ℕ) : ℕ :=
  if i < P then i else if i < P + b then i + a else if i < P + a + b then i - b else i

theorem swapIdx_lt {P a b n i : ℕ} (h : P + a + b ≤ n) (hi : i < n) : swapIdx P a b i < n := by
  unfold swapIdx
  split_ifs <;> omega

theorem swapIdx_swapIdx (P a b i : ℕ) : swapIdx P b a (swapIdx P a b i) = i := by
  unfold swapIdx
  split_ifs <;> omega

/-- The permutation exchanging two adjacent blocks of positions. -/
def swapPerm (P a b n : ℕ) (h : P + a + b ≤ n) : Equiv.Perm (Fin n) where
  toFun i := ⟨swapIdx P a b i, swapIdx_lt h i.2⟩
  invFun i := ⟨swapIdx P b a i, swapIdx_lt (by omega) i.2⟩
  left_inv i := Fin.ext (swapIdx_swapIdx P a b i)
  right_inv i := Fin.ext (swapIdx_swapIdx P b a i)

theorem swapPerm_val (P a b n : ℕ) (h : P + a + b ≤ n) (i : Fin n) :
    (swapPerm P a b n h i : ℕ) = swapIdx P a b i :=
  rfl

theorem realRank_singleton (u : RealBlock) : realRank [u] = u.rank := by
  rw [realRank_cons, realRank_nil, add_zero]

variable (pre post : List RealBlock) (u v : RealBlock)

open InductionStages

theorem pc_seg1 (i : ℕ) (hi : i < realRank pre) :
    realPositionCharacter (pre ++ u :: v :: post) i = realPositionCharacter pre i :=
  realPositionCharacter_append_right pre _ i hi

theorem pc_seg2 (j : ℕ) (hj : j < u.rank) :
    realPositionCharacter (pre ++ u :: v :: post) (realRank pre + j) =
      realPositionCharacter [u] j := by
  rw [realPositionCharacter_append_left, show u :: v :: post = [u] ++ (v :: post) from rfl,
    realPositionCharacter_append_right [u] _ j (by rwa [realRank_singleton])]

theorem pc_seg3 (j : ℕ) (hj : j < v.rank) :
    realPositionCharacter (pre ++ u :: v :: post) (realRank pre + u.rank + j) =
      realPositionCharacter [v] j := by
  rw [add_assoc, realPositionCharacter_append_left,
    show u :: v :: post = [u] ++ (v :: post) from rfl, ← realRank_singleton u,
    realPositionCharacter_append_left, show v :: post = [v] ++ post from rfl,
    realPositionCharacter_append_right [v] post j (by rwa [realRank_singleton])]

theorem pc_seg4 (j : ℕ) :
    realPositionCharacter (pre ++ u :: v :: post) (realRank pre + u.rank + v.rank + j) =
      realPositionCharacter post j := by
  rw [show realRank pre + u.rank + v.rank + j = realRank pre + (realRank [u, v] + j) by
      simp only [realRank_cons, realRank_nil]; omega,
    realPositionCharacter_append_left, show u :: v :: post = [u, v] ++ post from rfl,
    realPositionCharacter_append_left]

theorem ib_seg1 (i : ℕ) (hi : i < realRank pre) :
    realInducedBlockAt (pre ++ u :: v :: post) i = realInducedBlockAt pre i :=
  realInducedBlockAt_append_right pre _ i hi

theorem ib_seg2 (j : ℕ) (hj : j < u.rank) :
    realInducedBlockAt (pre ++ u :: v :: post) (realRank pre + j) =
      realInducedBlockAt [u] j := by
  rw [realInducedBlockAt_append_left, show u :: v :: post = [u] ++ (v :: post) from rfl,
    realInducedBlockAt_append_right [u] _ j (by rwa [realRank_singleton])]

theorem ib_seg3 (j : ℕ) (hj : j < v.rank) :
    realInducedBlockAt (pre ++ u :: v :: post) (realRank pre + u.rank + j) =
      realInducedBlockAt [v] j := by
  rw [add_assoc, realInducedBlockAt_append_left,
    show u :: v :: post = [u] ++ (v :: post) from rfl, ← realRank_singleton u,
    realInducedBlockAt_append_left, show v :: post = [v] ++ post from rfl,
    realInducedBlockAt_append_right [v] post j (by rwa [realRank_singleton])]

theorem ib_seg4 (j : ℕ) :
    realInducedBlockAt (pre ++ u :: v :: post) (realRank pre + u.rank + v.rank + j) =
      realInducedBlockAt post j := by
  rw [show realRank pre + u.rank + v.rank + j = realRank pre + (realRank [u, v] + j) by
      simp only [realRank_cons, realRank_nil]; omega,
    realInducedBlockAt_append_left, show u :: v :: post = [u, v] ++ post from rfl,
    realInducedBlockAt_append_left]

variable {pre post u v}

theorem realRank_swap :
    realRank (pre ++ u :: v :: post) = realRank pre + u.rank + v.rank + realRank post := by
  rw [realRank_append, realRank_cons, realRank_cons]
  omega

/-- The swap permutation carries the position characters of `pre ++ y :: x :: post` to those
of `pre ++ x :: y :: post`. -/
theorem swap_positionCharacter (x y : RealBlock) {n : ℕ}
    (hn : realRank (pre ++ x :: y :: post) = n) (i : Fin n) :
    realPositionCharacter (pre ++ y :: x :: post) i =
      realPositionCharacter (pre ++ x :: y :: post)
        (swapPerm (realRank pre) x.rank y.rank n
          (by rw [← hn, realRank_swap]; omega) i) := by
  rw [swapPerm_val]
  have hi : (i : ℕ) < realRank pre + x.rank + y.rank + realRank post := by
    have h := i.2
    have h2 := realRank_swap (pre := pre) (u := x) (v := y) (post := post)
    omega
  unfold swapIdx
  split_ifs with h1 h2 h3
  · rw [pc_seg1 pre post y x _ h1, pc_seg1 pre post x y _ h1]
  · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = realRank pre + j := ⟨i - realRank pre, by omega⟩
    rw [hj, pc_seg2 pre post y x j (by omega),
      show realRank pre + j + x.rank = realRank pre + x.rank + j by omega,
      pc_seg3 pre post x y j (by omega)]
  · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = realRank pre + y.rank + j :=
      ⟨i - realRank pre - y.rank, by omega⟩
    rw [hj, pc_seg3 pre post y x j (by omega),
      show realRank pre + y.rank + j - y.rank = realRank pre + j by omega,
      pc_seg2 pre post x y j (by omega)]
  · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = realRank pre + x.rank + y.rank + j :=
      ⟨i - realRank pre - x.rank - y.rank, by omega⟩
    rw [hj, pc_seg4 pre post x y j,
      show realRank pre + x.rank + y.rank + j = realRank pre + y.rank + x.rank + j by omega,
      pc_seg4 pre post y x j]

/-- The swap permutation carries the induction blocks of `pre ++ y :: x :: post` to those of
`pre ++ x :: y :: post`. -/
theorem swap_inducedBlock (x y : RealBlock) {n : ℕ}
    (hn : realRank (pre ++ x :: y :: post) = n) (p : ℕ) (d : ComplexCharacterData)
    (hd : realInducedBlockAt (pre ++ x :: y :: post) p = some d) :
    ∃ p' : ℕ, realInducedBlockAt (pre ++ y :: x :: post) p' = some d ∧
      ∀ i : Fin n, ((i : ℕ) = p' →
          (swapPerm (realRank pre) x.rank y.rank n (by rw [← hn, realRank_swap]; omega) i : ℕ) =
            p) ∧
        ((i : ℕ) = p' + 1 →
          (swapPerm (realRank pre) x.rank y.rank n (by rw [← hn, realRank_swap]; omega) i : ℕ) =
            p + 1) := by
  have hlt := realInducedBlockAt_lt hd
  rw [realRank_swap] at hlt
  by_cases h1 : p < realRank pre
  · have hb : realInducedBlockAt pre p = some d := by rwa [← ib_seg1 pre post x y p h1]
    have hp1 := realInducedBlockAt_lt hb
    refine ⟨p, by rw [ib_seg1 pre post y x p h1]; exact hb,
      fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩ <;>
    · rw [swapPerm_val, hi]
      unfold swapIdx
      split_ifs; omega
  by_cases h2 : p < realRank pre + x.rank
  · obtain ⟨j, hj⟩ : ∃ j, p = realRank pre + j := ⟨p - realRank pre, by omega⟩
    have hb : realInducedBlockAt [x] j = some d := by
      rwa [hj, ib_seg2 pre post x y j (by omega)] at hd
    have hj1 := realInducedBlockAt_lt hb
    rw [realRank_singleton] at hj1
    refine ⟨realRank pre + y.rank + j, by rw [ib_seg3 pre post y x j (by omega)]; exact hb,
      fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩ <;>
    · rw [swapPerm_val, hi]
      unfold swapIdx
      split_ifs <;> omega
  by_cases h3 : p < realRank pre + x.rank + y.rank
  · obtain ⟨j, hj⟩ : ∃ j, p = realRank pre + x.rank + j := ⟨p - realRank pre - x.rank, by omega⟩
    have hb : realInducedBlockAt [y] j = some d := by
      rwa [hj, ib_seg3 pre post x y j (by omega)] at hd
    have hj1 := realInducedBlockAt_lt hb
    rw [realRank_singleton] at hj1
    refine ⟨realRank pre + j, by rw [ib_seg2 pre post y x j (by omega)]; exact hb,
      fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩ <;>
    · rw [swapPerm_val, hi]
      unfold swapIdx
      split_ifs <;> omega
  · obtain ⟨j, hj⟩ : ∃ j, p = realRank pre + x.rank + y.rank + j :=
      ⟨p - realRank pre - x.rank - y.rank, by omega⟩
    have hb : realInducedBlockAt post j = some d := by
      rwa [hj, ib_seg4 pre post x y j] at hd
    refine ⟨p, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · rw [hj, show realRank pre + x.rank + y.rank + j = realRank pre + y.rank + x.rank + j by
        omega, ib_seg4 pre post y x j]
      exact hb
    all_goals
      rw [swapPerm_val, hi]
      unfold swapIdx
      split_ifs <;> omega

end Swap

end RealSwapSurjective

open Langlands.LocalFactor.Archimedean RealSwapSurjective in
/-- **Injective swaps are surjective** (`RealSwapInjectiveIntertwinerSurjectiveStatement`). -/
theorem realSwapInjectiveIntertwinerSurjective :
    RealSwapInjectiveIntertwinerSurjectiveStatement := by
  intro n pre post x y T hn hTi hT
  have hn' : realRank (pre ++ y :: x :: post) = n := by
    rw [← hn, realRank_swap, realRank_swap]
    omega
  obtain ⟨Φ, hΦ, hΦi⟩ := exists_perm_injection hn hn' (swap_positionCharacter x y hn)
    (swap_inducedBlock x y hn)
  exact surjective_of_injective (realStandardAdmissible n _) (realStandardAdmissible n _)
    (isRealGKModule_realStandardModule n _).1 (isRealGKModule_realStandardModule n _).2.1
    T (fun k v => hT.map_realStandardRep k v) hTi Φ hΦ hΦi

end Langlands.Archimedean
