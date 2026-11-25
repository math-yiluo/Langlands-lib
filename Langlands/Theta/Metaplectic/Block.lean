import Langlands.Theta.Metaplectic.SiegelParabolic
import Langlands.Theta.Metaplectic.WeylElement
import Langlands.Theta.Heisenberg.PartialFourier

/-!
# The composition rule, block compatibility and the "Weyl group"

GKT §2.2.2 (the scalar of `M_A(g₁) M_A(g₂) = c M_A(g₁ g₂)`, p. 52, and (2.11)), §2.3.3 ((2.21),
Proposition 2.24, (2.22), (2.23), Lemma 2.25, Proposition 2.26, pp. 61–66) and §2.3.4
(Proposition 2.28 and Corollary 2.29, pp. 66–68), for the standard Weil operator `r(g)` of
`Langlands.Theta.Metaplectic.StandardOperator`.

* `exists_standardOperator_comp`: **the composition rule** `r(g₁) r(g₂) = c r(g₁ g₂)` with
  `|c| = 1` (the existence of the Leray cocycle (2.11)).
* `blockDiag β₁ β₂ (g₁, g₂)` is the block diagonal isometry `diag(g₁, g₂)` of `W₁ ⊕ W₂` (for the
  orthogonal sum `sumPairing β₁ β₂` and the tensors `schwartzBruhatTensor φ₁ φ₂` of
  `Langlands.Theta.Heisenberg.PartialFourier`).
* `standardOperator_blockDiag`: **Proposition 2.28**, `r(diag(g₁, g₂)) (φ₁ ⊗ φ₂) =
  r₁(g₁) φ₁ ⊗ r₂(g₂) φ₂`; `standardOperator_blockDiag_comp`: **Corollary 2.29** in terms of the
  scalars of the composition rule.
* `standardOperator_weylIsometry_mul_self`, `standardOperator_weylIsometry_pow_comp`: **Lemma
  2.25** and **Proposition 2.26** for the powers of a Weyl element `w_J`.
* `standardOperator_partialWeylElement`, `standardOperator_partialWeylElement_mul_self`,
  `standardOperator_blockDiag_weyl_comp`: **(2.23)**, **Lemma 2.25** and **Proposition 2.26** for
  the partial Weyl elements `diag(w_J, 1)` and the group of the `diag(w_{J₁}^i, w_{J₂}^j)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w v₁ w₁ v₂ w₂

section Sum

variable {R : Type u} [CommRing R]
  {X₁ : Type v₁} {Y₁ : Type w₁} {X₂ : Type v₂} {Y₂ : Type w₂}
  [AddCommGroup X₁] [Module R X₁] [AddCommGroup Y₁] [Module R Y₁]
  [AddCommGroup X₂] [Module R X₂] [AddCommGroup Y₂] [Module R Y₂]
  (β₁ : X₁ →ₗ[R] Y₁ →ₗ[R] R) (β₂ : X₂ →ₗ[R] Y₂ →ₗ[R] R)

/-- The underlying linear automorphism of `diag(g₁, g₂)`. -/
def blockDiagEquiv (g₁ : (X₁ × Y₁) ≃ₗ[R] X₁ × Y₁) (g₂ : (X₂ × Y₂) ≃ₗ[R] X₂ × Y₂) :
    ((X₁ × X₂) × (Y₁ × Y₂)) ≃ₗ[R] (X₁ × X₂) × (Y₁ × Y₂) :=
  (LinearEquiv.prodProdProdComm R X₁ X₂ Y₁ Y₂).trans
    ((g₁.prodCongr g₂).trans (LinearEquiv.prodProdProdComm R X₁ X₂ Y₁ Y₂).symm)

theorem blockDiagEquiv_apply (g₁ : (X₁ × Y₁) ≃ₗ[R] X₁ × Y₁) (g₂ : (X₂ × Y₂) ≃ₗ[R] X₂ × Y₂)
    (w : (X₁ × X₂) × (Y₁ × Y₂)) :
    blockDiagEquiv g₁ g₂ w =
      (((g₁ (w.1.1, w.2.1)).1, (g₂ (w.1.2, w.2.2)).1),
        ((g₁ (w.1.1, w.2.1)).2, (g₂ (w.1.2, w.2.2)).2)) := rfl

/-- **The block diagonal isometry `diag(g₁, g₂)`** of `W₁ ⊕ W₂` (GKT §2.3.4, p. 67), as a group
homomorphism `Sp(W₁) × Sp(W₂) → Sp(W₁ ⊕ W₂)`. -/
def blockDiag : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂) →*
    isometryGroup (polarizedForm (sumPairing β₁ β₂)) where
  toFun g := ⟨blockDiagEquiv (g.1 : (X₁ × Y₁) ≃ₗ[R] X₁ × Y₁) (g.2 : (X₂ × Y₂) ≃ₗ[R] X₂ × Y₂),
    fun w w' => by
      rw [polarizedForm_sumPairing, polarizedForm_sumPairing, blockDiagEquiv_apply,
        blockDiagEquiv_apply]
      exact congrArg₂ (· + ·) (g.1.2 _ _) (g.2.2 _ _)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem blockDiag_apply (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂))
    (w : (X₁ × X₂) × (Y₁ × Y₂)) :
    ((blockDiag β₁ β₂ g : isometryGroup _) : _ ≃ₗ[R] _) w =
      blockDiagEquiv (g.1 : (X₁ × Y₁) ≃ₗ[R] X₁ × Y₁) (g.2 : (X₂ × Y₂) ≃ₗ[R] X₂ × Y₂) w := rfl

theorem isometryInv_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂))
    (w : (X₁ × X₂) × (Y₁ × Y₂)) :
    isometryInv (blockDiag β₁ β₂ g) w =
      (((isometryInv g.1 (w.1.1, w.2.1)).1, (isometryInv g.2 (w.1.2, w.2.2)).1),
        ((isometryInv g.1 (w.1.1, w.2.1)).2, (isometryInv g.2 (w.1.2, w.2.2)).2)) := by
  rw [isometryInv, ← map_inv]
  rfl

theorem standardC_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂)) (y : Y₁ × Y₂) :
    standardC (blockDiag β₁ β₂ g) y = (standardC g.1 y.1, standardC g.2 y.2) := by
  rw [standardC_apply, isometryInv_blockDiag]
  rfl

/-- **`ker c(diag(g₁, g₂)) = ker c(g₁) × ker c(g₂)`**. -/
theorem standardKernel_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂)) :
    standardKernel (blockDiag β₁ β₂ g) = (standardKernel g.1).prod (standardKernel g.2) := by
  ext y
  change standardC (blockDiag β₁ β₂ g) y = 0 ↔ standardC g.1 y.1 = 0 ∧ standardC g.2 y.2 = 0
  rw [standardC_blockDiag, Prod.mk_eq_zero]

variable {β₁ β₂} in
/-- `(Y₁ × Y₂) / ker c(diag(g₁, g₂)) ≃ Y₁ / ker c(g₁) × Y₂ / ker c(g₂)`. -/
def blockQuotientEquiv
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂)) :
    ((Y₁ × Y₂) ⧸ standardKernel (blockDiag β₁ β₂ g)) ≃ₗ[R]
      (Y₁ ⧸ standardKernel g.1) × (Y₂ ⧸ standardKernel g.2) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [standardKernel_blockDiag, LinearMap.ker_prodMap, Submodule.ker_mkQ,
      Submodule.ker_mkQ])).trans
    (LinearMap.quotKerEquivOfSurjective ((standardKernel g.1).mkQ.prodMap (standardKernel g.2).mkQ)
      (fun q => by
        obtain ⟨y₁, hy₁⟩ := Submodule.mkQ_surjective _ q.1
        obtain ⟨y₂, hy₂⟩ := Submodule.mkQ_surjective _ q.2
        exact ⟨(y₁, y₂), Prod.ext hy₁ hy₂⟩))

variable {β₁ β₂} in
theorem blockQuotientEquiv_mk
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂)) (y : Y₁ × Y₂) :
    blockQuotientEquiv g (Submodule.Quotient.mk y) =
      (Submodule.Quotient.mk y.1, Submodule.Quotient.mk y.2) := rfl

variable [Invertible (2 : R)] (ψ : AddChar R ℂ)

/-- The integrand of `r(diag(g₁, g₂))` at `φ₁ ⊗ φ₂` is the product of the integrands. -/
theorem standardIntegrand_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂))
    (φ₁ : X₁ → ℂ) (φ₂ : X₂ → ℂ) (x : X₁ × X₂) (y : Y₁ × Y₂) :
    standardIntegrand ψ (blockDiag β₁ β₂ g) (fun x => φ₁ x.1 * φ₂ x.2) x y =
      standardIntegrand ψ g.1 φ₁ x.1 y.1 * standardIntegrand ψ g.2 φ₂ x.2 y.2 := by
  simp only [standardIntegrand, isometryInv_blockDiag, sumPairing_apply]
  set a := isometryInv g.1 (x.1, y.1)
  set b := isometryInv g.2 (x.2, y.2)
  have h : ⅟2 * (β₁ a.1 a.2 + β₂ b.1 b.2) - ⅟2 * (β₁ x.1 y.1 + β₂ x.2 y.2) =
      (⅟2 * β₁ a.1 a.2 - ⅟2 * β₁ x.1 y.1) + (⅟2 * β₂ b.1 b.2 - ⅟2 * β₂ x.2 y.2) := by ring
  rw [h, AddChar.map_add_eq_mul]
  ring

end Sum

section CompositionRule

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

/-- **The composition rule** (GKT p. 52 and (2.11)): `r(g₁) r(g₂) = c r(g₁ g₂)` with `|c| = 1`.
Both sides intertwine the Schrödinger model with its composition with `g₁ g₂`, so they differ by
a scalar (Schur's lemma, `MetaplecticGroup.exists_scalar_mul_eq`), of absolute value `1` since
both are unitary. -/
theorem exists_standardOperator_comp (g₁ g₂ : isometryGroup (polarizedForm β)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ standardOperator hψ hψ1 g₁ ∘ₗ standardOperator hψ hψ1 g₂ =
      c • standardOperator hψ hψ1 (g₁ * g₂) := by
  have := locallyCompactSpace_of_finiteDimensional F X
  have := compactOpenExhaustion_of_finiteDimensional F X
  obtain ⟨z, hz⟩ := MetaplecticGroup.exists_scalar_mul_eq (isSmooth_schrodingerSB hψ _)
    (isIrreducible_schrodingerSB hψ hψ1 _) (x := standardPair hψ hψ1 (g₁ * g₂))
    (y := standardPair hψ hψ1 g₁ * standardPair hψ hψ1 g₂) (by rw [map_mul]; rfl)
  have hop : standardOperator hψ hψ1 g₁ ∘ₗ standardOperator hψ hψ1 g₂ =
      (z : ℂ) • standardOperator hψ hψ1 (g₁ * g₂) := LinearMap.ext fun φ => by
    have h := congrArg (fun x => MetaplecticGroup.weil _ x φ) hz
    simp only [map_mul, Module.End.mul_apply, weil_standardPair,
      MetaplecticGroup.weil_scalar] at h
    exact h
  refine ⟨z, ?_, hop⟩
  obtain ⟨e, he⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure X)
  have h1 := standardOperator_inner hψ hψ1 (g₁ * g₂) Measure.addHaar e e
  have h2 : schwartzBruhatInner Measure.addHaar
      (standardOperator hψ hψ1 g₁ (standardOperator hψ hψ1 g₂ e))
      (standardOperator hψ hψ1 g₁ (standardOperator hψ hψ1 g₂ e)) =
        schwartzBruhatInner Measure.addHaar e e := by
    rw [standardOperator_inner, standardOperator_inner]
  rw [show standardOperator hψ hψ1 g₁ (standardOperator hψ hψ1 g₂ e) =
    (z : ℂ) • standardOperator hψ hψ1 (g₁ * g₂) e from LinearMap.congr_fun hop e] at h2
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, h1,
    ← mul_assoc, Complex.mul_conj'] at h2
  have h3 : ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have := mul_right_cancel₀ he (h2.trans (one_mul _).symm)
    exact_mod_cast this
  have h4 : ‖(z : ℂ)‖ ^ 2 = 1 ^ 2 := by rw [one_pow]; exact_mod_cast h3
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h4

end CompositionRule

section WeylGroup

variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] {β : X →ₗ[R] Y →ₗ[R] R}

/-- `w_J⁻² = -1`: `w_J² (x, y) = (-x, -y)`. -/
theorem isometryInv_weylIsometry_mul_self (J : Y ≃ₗ[R] X)
    (hJ : ∀ y y', β (J y) y' = β (J y') y) (v : X × Y) :
    isometryInv (weylIsometry β J hJ * weylIsometry β J hJ) v = -v := by
  rw [isometryInv, mul_inv_rev]
  change isometryInv (weylIsometry β J hJ) (isometryInv (weylIsometry β J hJ) v) = -v
  rw [isometryInv_weylIsometry, isometryInv_weylIsometry]
  ext <;> simp

/-- **`w_J² = a`** lies in the Siegel parabolic (GKT p. 62, `w_S² = a_S`). -/
theorem weylIsometry_mul_self_mem (J : Y ≃ₗ[R] X) (hJ : ∀ y y', β (J y) y' = β (J y') y) :
    weylIsometry β J hJ * weylIsometry β J hJ ∈ siegelParabolicGroup β := by
  intro y
  refine ⟨?_, ?_⟩
  · change ((weylIsometry β J hJ : (X × Y) ≃ₗ[R] X × Y)
      ((weylIsometry β J hJ : (X × Y) ≃ₗ[R] X × Y) (0, y))).1 = 0
    simp [weylIsometry_apply]
  · rw [isometryInv_weylIsometry_mul_self]
    simp

end WeylGroup

section WeylLocal

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {β : X →ₗ[F] Y →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [β.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

/-- **GKT Lemma 2.25 for `a = w_J²`** (Lemma 2.16): `r(w_J²) φ(x) = φ(-x)`. -/
theorem standardOperator_weylIsometry_mul_self_apply (J : Y ≃ₗ[F] X)
    (hJ : ∀ y y', β (J y) y' = β (J y') y) (φ : SchwartzBruhat X) (x : X) :
    (standardOperator hψ hψ1 (weylIsometry β J hJ * weylIsometry β J hJ) φ : X → ℂ) x =
      (φ : X → ℂ) (-x) := by
  have hp := weylIsometry_mul_self_mem J hJ
  have hD : ∀ x', standardD (weylIsometry β J hJ * weylIsometry β J hJ) x' = -x' := fun x' => by
    change (isometryInv (weylIsometry β J hJ * weylIsometry β J hJ) (x', 0)).1 = -x'
    rw [isometryInv_weylIsometry_mul_self]
    rfl
  have hB : ∀ x', standardB (weylIsometry β J hJ * weylIsometry β J hJ) x' = 0 := fun x' => by
    change (isometryInv (weylIsometry β J hJ * weylIsometry β J hJ) (x', 0)).2 = 0
    rw [isometryInv_weylIsometry_mul_self]
    simp
  have hdd : siegelD hp * siegelD hp = 1 := LinearEquiv.ext fun x' => by
    change siegelD hp (siegelD hp x') = x'
    rw [siegelD_apply, siegelD_apply, hD, hD, neg_neg]
  have hχ : distribHaarChar F (LinearEquiv.det (siegelD hp)) = 1 := by
    have h2 : distribHaarChar F (LinearEquiv.det (siegelD hp)) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, sq, hdd, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  rw [standardOperator_of_mem_siegelParabolicGroup hψ hψ1 hp, hχ, hD, hB, map_zero, mul_zero,
    AddChar.map_zero_eq_one]
  simp

/-- **GKT Lemma 2.25** for the Weyl element `w_J`: `r(w_J)² φ(x) = φ(-x)` (Fourier inversion for
the self-dual measure). -/
theorem standardOperator_weylIsometry_weylIsometry_apply (J : Y ≃ₗ[F] X)
    (hJ : ∀ y y', β (J y) y' = β (J y') y) (φ : SchwartzBruhat X) (x : X) :
    (standardOperator hψ hψ1 (weylIsometry β J hJ)
        (standardOperator hψ hψ1 (weylIsometry β J hJ) φ) : X → ℂ) x = (φ : X → ℂ) (-x) := by
  have := locallyCompactSpace_of_finiteDimensional F X
  have := secondCountableTopology_of_finiteDimensional F X
  have := compactOpenExhaustion_of_finiteDimensional F X
  have he := isSelfDualBicharacter_weylBicharacter hψ hψ1 J hJ
  rw [standardOperator_weylIsometry]
  have h1 : (standardOperator hψ hψ1 (weylIsometry β J hJ) φ : X → ℂ) =
      bicharacterFourier (selfDualMeasure (weylBicharacter ψ β J)) (weylBicharacter ψ β J) φ :=
    funext fun u => standardOperator_weylIsometry hψ hψ1 J hJ φ u
  rw [h1]
  exact bicharacterFourier_bicharacterFourier_selfDualMeasure he φ.2 x

/-- **GKT Lemma 2.25**: `r(w_J)² = r(w_J²)`. -/
theorem standardOperator_weylIsometry_mul_self (J : Y ≃ₗ[F] X)
    (hJ : ∀ y y', β (J y) y' = β (J y') y) :
    standardOperator hψ hψ1 (weylIsometry β J hJ) ∘ₗ standardOperator hψ hψ1 (weylIsometry β J hJ) =
      standardOperator hψ hψ1 (weylIsometry β J hJ * weylIsometry β J hJ) :=
  LinearMap.ext fun φ => Subtype.ext <| funext fun x => by
    rw [LinearMap.comp_apply, standardOperator_weylIsometry_weylIsometry_apply,
      standardOperator_weylIsometry_mul_self_apply]

/-- **GKT Proposition 2.26 for the powers of `w_J`**: `r(w_J^i) r(w_J^j) = r(w_J^{i + j})`. -/
theorem standardOperator_weylIsometry_pow_comp (J : Y ≃ₗ[F] X)
    (hJ : ∀ y y', β (J y) y' = β (J y') y) (i j : ℕ) :
    standardOperator hψ hψ1 (weylIsometry β J hJ ^ i) ∘ₗ
        standardOperator hψ hψ1 (weylIsometry β J hJ ^ j) =
      standardOperator hψ hψ1 (weylIsometry β J hJ ^ (i + j)) := by
  set w := weylIsometry β J hJ
  set r := standardOperator hψ hψ1 (β := β)
  have h0 : r 1 = LinearMap.id := standardOperator_one hψ hψ1
  have hP : w ^ 2 ∈ siegelParabolicGroup β := by rw [sq]; exact weylIsometry_mul_self_mem J hJ
  have h2 : r (w ^ 2) = r w ∘ₗ r w := by
    rw [sq]; exact (standardOperator_weylIsometry_mul_self hψ hψ1 J hJ).symm
  -- `r(w^{n+2}) = r(w²) r(w^n) = r(w^n) r(w²)` (Proposition 2.17)
  have hL : ∀ n, r (w ^ (n + 2)) = r (w ^ 2) ∘ₗ r (w ^ n) := fun n => by
    rw [add_comm, pow_add]; exact standardOperator_mul_of_mem_left hψ hψ1 _ hP
  have hR : ∀ n, r (w ^ (n + 2)) = r (w ^ n) ∘ₗ r (w ^ 2) := fun n => by
    rw [pow_add]; exact standardOperator_mul_of_mem_right hψ hψ1 _ hP
  have h1 : ∀ j, r w ∘ₗ r (w ^ j) = r (w ^ (1 + j)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      match j, ih with
      | 0, _ => rw [pow_zero, h0, LinearMap.comp_id, add_zero, pow_one]
      | 1, _ => rw [pow_one, ← h2]
      | k + 2, ih =>
        rw [hR k, ← LinearMap.comp_assoc, ih k (by omega),
          show 1 + (k + 2) = (1 + k) + 2 by ring, hR (1 + k)]
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ => rw [pow_zero, h0, LinearMap.id_comp, zero_add]
    | 1, _ => rw [pow_one, h1]
    | k + 2, ih =>
      rw [hL k, LinearMap.comp_assoc, ih k (by omega), show k + 2 + j = (k + j) + 2 by ring,
        hL (k + j)]

end WeylLocal

section PartialWeyl

variable {R : Type u} [CommRing R]
  {X₁ : Type v₁} {Y₁ : Type w₁} {X₂ : Type v₂} {Y₂ : Type w₂}
  [AddCommGroup X₁] [Module R X₁] [AddCommGroup Y₁] [Module R Y₁]
  [AddCommGroup X₂] [Module R X₂] [AddCommGroup Y₂] [Module R Y₂]
  {β₁ : X₁ →ₗ[R] Y₁ →ₗ[R] R}

variable (β₂ : X₂ →ₗ[R] Y₂ →ₗ[R] R) in
/-- **The partial Weyl element `w_S = diag(w_J, 1)`** of `W = W_S ⊕ W_{S^c}` (GKT (2.21), for
`W_S = X₁ × Y₁` and `J` the book's `I_S`). -/
def partialWeylElement (J : Y₁ ≃ₗ[R] X₁) (hJ : ∀ y y', β₁ (J y) y' = β₁ (J y') y) :
    isometryGroup (polarizedForm (sumPairing β₁ β₂)) :=
  blockDiag β₁ β₂ (weylIsometry β₁ J hJ, 1)

end PartialWeyl

section BlockLocal

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X₁ : Type v₁} [AddCommGroup X₁] [Module F X₁] [FiniteDimensional F X₁] [TopologicalSpace X₁]
  [IsModuleTopology F X₁] [IsTopologicalAddGroup X₁]
  {Y₁ : Type w₁} [AddCommGroup Y₁] [Module F Y₁] [FiniteDimensional F Y₁] [TopologicalSpace Y₁]
  [IsModuleTopology F Y₁]
  {X₂ : Type v₂} [AddCommGroup X₂] [Module F X₂] [FiniteDimensional F X₂] [TopologicalSpace X₂]
  [IsModuleTopology F X₂] [IsTopologicalAddGroup X₂]
  {Y₂ : Type w₂} [AddCommGroup Y₂] [Module F Y₂] [FiniteDimensional F Y₂] [TopologicalSpace Y₂]
  [IsModuleTopology F Y₂]
  {β₁ : X₁ →ₗ[F] Y₁ →ₗ[F] F} {β₂ : X₂ →ₗ[F] Y₂ →ₗ[F] F} {ψ : AddChar F ℂ}

variable [MeasurableSpace X₁] [BorelSpace X₁] [MeasurableSpace Y₁] [BorelSpace Y₁]
  [MeasurableSpace X₂] [BorelSpace X₂] [MeasurableSpace Y₂] [BorelSpace Y₂]
  [SecondCountableTopology X₁] [SecondCountableTopology Y₁]

omit [FiniteDimensional F X₁] [TopologicalSpace X₁] [IsModuleTopology F X₁]
  [IsTopologicalAddGroup X₁] [FiniteDimensional F Y₁] [FiniteDimensional F X₂] [TopologicalSpace X₂]
  [IsModuleTopology F X₂] [IsTopologicalAddGroup X₂] [MeasurableSpace X₁] [BorelSpace X₁]
  [MeasurableSpace X₂] [BorelSpace X₂] [SecondCountableTopology X₁] in
/-- **Fubini for `r(diag(g₁, g₂))`**: for measures `μ₁`, `μ₂` on `Y₁ / ker c(g₁)` and
`Y₂ / ker c(g₂)`, the operator of `diag(g₁, g₂)` for their product carries `φ₁ ⊗ φ₂` to
`r_{μ₁}(g₁) φ₁ ⊗ r_{μ₂}(g₂) φ₂`. -/
theorem standardOperatorFun_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂))
    (μ₁ : Measure (Y₁ ⧸ standardKernel g.1)) (μ₂ : Measure (Y₂ ⧸ standardKernel g.2))
    [SFinite μ₁] [SFinite μ₂] (φ₁ : X₁ → ℂ) (φ₂ : X₂ → ℂ) (x : X₁ × X₂) :
    standardOperatorFun ψ (blockDiag β₁ β₂ g) ((μ₁.prod μ₂).map (blockQuotientEquiv g).symm)
        (fun x => φ₁ x.1 * φ₂ x.2) x =
      standardOperatorFun ψ g.1 μ₁ φ₁ x.1 * standardOperatorFun ψ g.2 μ₂ φ₂ x.2 := by
  let E := (linearEquivToContinuousAddEquiv
    (blockQuotientEquiv (β₁ := β₁) (β₂ := β₂) g).symm).toHomeomorph.toMeasurableEquiv
  change ∫ q, standardIntegrandQ ψ (blockDiag β₁ β₂ g) (fun x => φ₁ x.1 * φ₂ x.2) x q
      ∂((μ₁.prod μ₂).map E) =
    (∫ q, standardIntegrandQ ψ g.1 φ₁ x.1 q ∂μ₁) * ∫ q, standardIntegrandQ ψ g.2 φ₂ x.2 q ∂μ₂
  rw [integral_map_equiv E, ← integral_prod_mul]
  congr 1
  funext q
  obtain ⟨q₁, q₂⟩ := q
  induction q₁ using Submodule.Quotient.induction_on with | H y₁ => ?_
  induction q₂ using Submodule.Quotient.induction_on with | H y₂ => ?_
  have hE : E (Submodule.Quotient.mk y₁, Submodule.Quotient.mk y₂) =
      Submodule.Quotient.mk (y₁, y₂) := by
    change (blockQuotientEquiv g).symm (Submodule.Quotient.mk y₁, Submodule.Quotient.mk y₂) = _
    exact (LinearEquiv.symm_apply_eq _).2 rfl
  rw [hE, standardIntegrandQ_mk, standardIntegrandQ_mk, standardIntegrandQ_mk,
    standardIntegrand_blockDiag]

variable [β₁.IsPerfPair] [β₂.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

/-- `r(diag(g₁, g₂)) (φ₁ ⊗ φ₂) = r(g₁) φ₁ ⊗ r(g₂) φ₂` up to a positive constant, before unitarity
is used. -/
theorem exists_standardOperator_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂),
      ((c : ℝ) : ℂ) • standardOperator hψ hψ1 (blockDiag β₁ β₂ g) (schwartzBruhatTensor φ₁ φ₂) =
        schwartzBruhatTensor (standardOperator hψ hψ1 g.1 φ₁) (standardOperator hψ hψ1 g.2 φ₂) := by
  have := secondCountableTopology_of_finiteDimensional F (Y₁ ⧸ standardKernel g.1)
  have := secondCountableTopology_of_finiteDimensional F (Y₂ ⧸ standardKernel g.2)
  obtain ⟨c, hc, hmap⟩ := exists_map_eq_smul
    ((standardMeasure hψ hψ1 g.1).prod (standardMeasure hψ hψ1 g.2))
    (standardMeasure hψ hψ1 (blockDiag β₁ β₂ g)) (blockQuotientEquiv g).symm
  refine ⟨c, hc, fun φ₁ φ₂ => Subtype.ext (funext fun x => ?_)⟩
  have h := standardOperatorFun_blockDiag (ψ := ψ) g (standardMeasure hψ hψ1 g.1)
    (standardMeasure hψ hψ1 g.2) φ₁ φ₂ x
  rw [hmap] at h
  change ((c : ℝ) : ℂ) * ∫ q, standardIntegrandQ ψ (blockDiag β₁ β₂ g)
      (fun x => (φ₁ : X₁ → ℂ) x.1 * (φ₂ : X₂ → ℂ) x.2) x q
      ∂(standardMeasure hψ hψ1 (blockDiag β₁ β₂ g)) =
    standardOperatorFun ψ g.1 (standardMeasure hψ hψ1 g.1) φ₁ x.1 *
      standardOperatorFun ψ g.2 (standardMeasure hψ hψ1 g.2) φ₂ x.2
  rw [← h]
  change _ = ∫ q, _ ∂(c • standardMeasure hψ hψ1 (blockDiag β₁ β₂ g))
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- **GKT Proposition 2.28** (block compatibility): `r(diag(g₁, g₂)) (φ₁ ⊗ φ₂) =
r₁(g₁) φ₁ ⊗ r₂(g₂) φ₂`. The book deduces it from the Bruhat decomposition and the splittings of
`P(X)` and of the "Weyl group"; here it is computed: `ker c` is the product of the kernels, the
integral over the product of the quotients is the product of the integrals (Fubini), and the
positive constant between the product of the measures `d_{g₁} × d_{g₂}` and `d_{diag(g₁, g₂)}` is
`1` by unitarity. -/
theorem standardOperator_blockDiag
    (g : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂))
    (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂) :
    standardOperator hψ hψ1 (blockDiag β₁ β₂ g) (schwartzBruhatTensor φ₁ φ₂) =
      schwartzBruhatTensor (standardOperator hψ hψ1 g.1 φ₁) (standardOperator hψ hψ1 g.2 φ₂) := by
  have := locallyCompactSpace_of_finiteDimensional F X₁
  have := locallyCompactSpace_of_finiteDimensional F X₂
  have := secondCountableTopology_of_finiteDimensional F X₂
  have := compactOpenExhaustion_of_finiteDimensional F X₁
  have := compactOpenExhaustion_of_finiteDimensional F X₂
  obtain ⟨c, hc, h⟩ := exists_standardOperator_blockDiag hψ hψ1 g
  obtain ⟨e₁, he₁⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure X₁)
  obtain ⟨e₂, he₂⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure X₂)
  set ν₁ : Measure X₁ := Measure.addHaar
  set ν₂ : Measure X₂ := Measure.addHaar
  have hu := standardOperator_inner hψ hψ1 (blockDiag β₁ β₂ g) (ν₁.prod ν₂)
    (schwartzBruhatTensor e₁ e₂) (schwartzBruhatTensor e₁ e₂)
  have h' := congrArg (fun v => schwartzBruhatInner (ν₁.prod ν₂) v v) (h e₁ e₂)
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal, hu,
    schwartzBruhatInner_tensor, standardOperator_inner] at h'
  have hc1 : ((c : ℝ) : ℂ) * (c : ℝ) = 1 := by
    have := mul_ne_zero he₁ he₂
    exact mul_right_cancel₀ this ((mul_assoc _ _ _).trans (h'.trans (one_mul _).symm))
  have hc2 : (c : ℝ) = 1 := by
    have h2 : (c : ℝ) * c = 1 := by exact_mod_cast hc1
    nlinarith [NNReal.coe_nonneg c]
  rw [← h, hc2, Complex.ofReal_one, one_smul]

/-- **GKT Corollary 2.29** (block compatibility of the scalars of the composition rule): if
`r₁(g₁) r₁(g₁') = c₁ r₁(g₁ g₁')` and `r₂(g₂) r₂(g₂') = c₂ r₂(g₂ g₂')`, then
`r(diag(g₁, g₂)) r(diag(g₁', g₂')) = c₁ c₂ r(diag(g₁ g₁', g₂ g₂'))`. -/
theorem standardOperator_blockDiag_comp
    (g g' : isometryGroup (polarizedForm β₁) × isometryGroup (polarizedForm β₂)) {c₁ c₂ : ℂ}
    (h₁ : standardOperator hψ hψ1 g.1 ∘ₗ standardOperator hψ hψ1 g'.1 =
      c₁ • standardOperator hψ hψ1 (g.1 * g'.1))
    (h₂ : standardOperator hψ hψ1 g.2 ∘ₗ standardOperator hψ hψ1 g'.2 =
      c₂ • standardOperator hψ hψ1 (g.2 * g'.2)) :
    standardOperator hψ hψ1 (blockDiag β₁ β₂ g) ∘ₗ standardOperator hψ hψ1 (blockDiag β₁ β₂ g') =
      (c₁ * c₂) • standardOperator hψ hψ1 (blockDiag β₁ β₂ (g * g')) := by
  have := locallyCompactSpace_of_finiteDimensional F X₁
  have := locallyCompactSpace_of_finiteDimensional F X₂
  have := secondCountableTopology_of_finiteDimensional F X₂
  have := compactOpenExhaustion_of_finiteDimensional F X₁
  have := compactOpenExhaustion_of_finiteDimensional F X₂
  obtain ⟨c, -, hc⟩ := exists_standardOperator_comp hψ hψ1 (blockDiag β₁ β₂ g) (blockDiag β₁ β₂ g')
  rw [← map_mul] at hc
  obtain ⟨e₁, he₁⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure X₁)
  obtain ⟨e₂, he₂⟩ := exists_schwartzBruhatInner_ne_zero (Measure.addHaar : Measure X₂)
  have hv : standardOperator hψ hψ1 (blockDiag β₁ β₂ (g * g')) (schwartzBruhatTensor e₁ e₂) ≠ 0 :=
    fun h0 => by
      have hu := standardOperator_inner hψ hψ1 (blockDiag β₁ β₂ (g * g'))
        ((Measure.addHaar : Measure X₁).prod (Measure.addHaar : Measure X₂))
        (schwartzBruhatTensor e₁ e₂) (schwartzBruhatTensor e₁ e₂)
      rw [h0, map_zero, schwartzBruhatInner_tensor] at hu
      exact mul_ne_zero he₁ he₂ hu.symm
  have hL : (standardOperator hψ hψ1 (blockDiag β₁ β₂ g) ∘ₗ
      standardOperator hψ hψ1 (blockDiag β₁ β₂ g')) (schwartzBruhatTensor e₁ e₂) =
        (c₁ * c₂) • standardOperator hψ hψ1 (blockDiag β₁ β₂ (g * g'))
          (schwartzBruhatTensor e₁ e₂) := by
    rw [LinearMap.comp_apply, standardOperator_blockDiag, standardOperator_blockDiag,
      ← LinearMap.comp_apply (standardOperator hψ hψ1 g.1), h₁,
      ← LinearMap.comp_apply (standardOperator hψ hψ1 g.2), h₂, LinearMap.smul_apply,
      LinearMap.smul_apply, schwartzBruhatTensor_smul, standardOperator_blockDiag]
    rfl
  have hR : (standardOperator hψ hψ1 (blockDiag β₁ β₂ g) ∘ₗ
      standardOperator hψ hψ1 (blockDiag β₁ β₂ g')) (schwartzBruhatTensor e₁ e₂) =
        c • standardOperator hψ hψ1 (blockDiag β₁ β₂ (g * g')) (schwartzBruhatTensor e₁ e₂) := by
    rw [hc]
    rfl
  have hcc : c = c₁ * c₂ := smul_left_injective ℂ hv (hR.symm.trans hL)
  rw [hc, hcc]

/-- **GKT (2.23)**: the partial Weyl element acts by the partial Fourier transform,
`r(w_S) (φ₁ ⊗ φ₂) = ℱ φ₁ ⊗ φ₂`, `ℱ φ₁ (x) = ∫ ψ(-β₁(x, J⁻¹ u)) φ₁(u) du` for the self-dual
measure (Proposition 2.24). -/
theorem standardOperator_partialWeylElement (J : Y₁ ≃ₗ[F] X₁)
    (hJ : ∀ y y', β₁ (J y) y' = β₁ (J y') y) (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂)
    (x : X₁ × X₂) :
    (standardOperator hψ hψ1 (partialWeylElement β₂ J hJ) (schwartzBruhatTensor φ₁ φ₂) :
        X₁ × X₂ → ℂ) x =
      (∫ u, weylBicharacter ψ β₁ J x.1 u * (φ₁ : X₁ → ℂ) u
        ∂(selfDualMeasure (weylBicharacter ψ β₁ J))) * (φ₂ : X₂ → ℂ) x.2 := by
  rw [partialWeylElement, standardOperator_blockDiag, schwartzBruhatTensor_apply,
    standardOperator_weylIsometry, standardOperator_one]
  rfl

/-- **GKT Lemma 2.25** for a partial Weyl element: `r(w_S)² = r(w_S²)` (and
`w_S² = diag(w_J², 1) = a_S`). -/
theorem standardOperator_partialWeylElement_mul_self (J : Y₁ ≃ₗ[F] X₁)
    (hJ : ∀ y y', β₁ (J y) y' = β₁ (J y') y) :
    standardOperator hψ hψ1 (partialWeylElement β₂ J hJ) ∘ₗ
        standardOperator hψ hψ1 (partialWeylElement β₂ J hJ) =
      standardOperator hψ hψ1 (partialWeylElement β₂ J hJ * partialWeylElement β₂ J hJ) := by
  have h := standardOperator_blockDiag_comp hψ hψ1 (weylIsometry β₁ J hJ, 1)
    (weylIsometry β₁ J hJ, (1 : isometryGroup (polarizedForm β₂))) (c₁ := 1) (c₂ := 1)
    (by rw [one_smul]; exact standardOperator_weylIsometry_mul_self hψ hψ1 J hJ)
    (by rw [one_smul, standardOperator_one, mul_one, standardOperator_one, LinearMap.id_comp])
  rw [one_mul, one_smul, map_mul] at h
  exact h

/-- **GKT Lemma 2.25**, pointwise: `r(w_S²) (φ₁ ⊗ φ₂) (x₁, x₂) = φ₁(-x₁) φ₂(x₂)`. -/
theorem standardOperator_partialWeylElement_mul_self_apply (J : Y₁ ≃ₗ[F] X₁)
    (hJ : ∀ y y', β₁ (J y) y' = β₁ (J y') y) (φ₁ : SchwartzBruhat X₁) (φ₂ : SchwartzBruhat X₂)
    (x : X₁ × X₂) :
    (standardOperator hψ hψ1 (partialWeylElement β₂ J hJ * partialWeylElement β₂ J hJ)
        (schwartzBruhatTensor φ₁ φ₂) : X₁ × X₂ → ℂ) x =
      (φ₁ : X₁ → ℂ) (-x.1) * (φ₂ : X₂ → ℂ) x.2 := by
  rw [partialWeylElement, ← map_mul, standardOperator_blockDiag, schwartzBruhatTensor_apply]
  change (standardOperator hψ hψ1 (weylIsometry β₁ J hJ * weylIsometry β₁ J hJ) φ₁ : X₁ → ℂ) x.1 *
      (standardOperator hψ hψ1 (1 * 1 : isometryGroup (polarizedForm β₂)) φ₂ : X₂ → ℂ) x.2 = _
  rw [standardOperator_weylIsometry_mul_self_apply, mul_one, standardOperator_one]
  rfl

/-- **GKT Proposition 2.26** for the group of the `diag(w_{J₁}^i, w_{J₂}^j)` (for one-dimensional
blocks, the book's "Weyl group" `W` of a standard basis of rank two; iterating the blocks gives
the rank `n`): `r` is multiplicative on it. -/
theorem standardOperator_blockDiag_weyl_comp (J₁ : Y₁ ≃ₗ[F] X₁)
    (hJ₁ : ∀ y y', β₁ (J₁ y) y' = β₁ (J₁ y') y) (J₂ : Y₂ ≃ₗ[F] X₂)
    (hJ₂ : ∀ y y', β₂ (J₂ y) y' = β₂ (J₂ y') y) (i₁ i₂ j₁ j₂ : ℕ) :
    standardOperator hψ hψ1 (blockDiag β₁ β₂ (weylIsometry β₁ J₁ hJ₁ ^ i₁,
        weylIsometry β₂ J₂ hJ₂ ^ i₂)) ∘ₗ
      standardOperator hψ hψ1 (blockDiag β₁ β₂ (weylIsometry β₁ J₁ hJ₁ ^ j₁,
        weylIsometry β₂ J₂ hJ₂ ^ j₂)) =
    standardOperator hψ hψ1 (blockDiag β₁ β₂ (weylIsometry β₁ J₁ hJ₁ ^ i₁,
        weylIsometry β₂ J₂ hJ₂ ^ i₂) * blockDiag β₁ β₂ (weylIsometry β₁ J₁ hJ₁ ^ j₁,
        weylIsometry β₂ J₂ hJ₂ ^ j₂)) := by
  have h := standardOperator_blockDiag_comp hψ hψ1 (weylIsometry β₁ J₁ hJ₁ ^ i₁,
    weylIsometry β₂ J₂ hJ₂ ^ i₂) (weylIsometry β₁ J₁ hJ₁ ^ j₁, weylIsometry β₂ J₂ hJ₂ ^ j₂)
    (c₁ := 1) (c₂ := 1)
    (by rw [one_smul, ← pow_add]; exact standardOperator_weylIsometry_pow_comp hψ hψ1 J₁ hJ₁ _ _)
    (by rw [one_smul, ← pow_add]; exact standardOperator_weylIsometry_pow_comp hψ hψ1 J₂ hJ₂ _ _)
  rw [one_mul, one_smul, map_mul] at h
  exact h

end BlockLocal

end Langlands.Theta
