import Langlands.Representation.Archimedean.ComplexStandardHomTranspose
import Langlands.Representation.Archimedean.ComplexDuality.Pairing
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Langlands.Representation.KFiniteDual
import Langlands.Global.ArchimedeanCompact

/-!
# Proof of the transposition of intertwinings between complex principal series

`complexStandardHomTranspose` proves `ComplexStandardHomTransposeStatement`. For lists of
complex characters `ds` and `ds'` with pointwise inverse position characters, the integration
pairing `⟨g, h⟩ = ∫_{U(n)} g(k) h(k) dk` of `X(ds')` with `X(ds)` is invariant and
nondegenerate in both arguments, and every `U(n)`-finite linear functional on `X(ds)` is
`⟨g, ·⟩` for a unique `g ∈ X(ds')`. The transpose `T'` of a nonzero intertwining map
`T : X(d) → X(c)` is then defined by `⟨T' f, h⟩_d = ⟨f, T h⟩_c`.
-/

noncomputable section

open scoped TensorProduct Matrix MonoidAlgebra

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexStandardHomTransposeProof

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Archimedean.ComplexDuality
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

/-! ## Admissibility of the complex principal series -/

section Admissible

variable {n : ℕ} (χ : ℕ → ℂˣ → ℂ)

/-- The value at the identity of the image of a `U(n)`-intertwiner into the `U(n)`-finite
functions of a complex principal series: the linear functional `x ↦ (T x)(1)`. -/
def complexValueAtOne (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners (principalSeriesRep ℂ n χ) d τ →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] ℂ) where
  toFun T :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℂ => ℂ) 1).comp
      ((kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)).subtype.comp
        (T : (Fin d → ℂ) →ₗ[ℂ] _))
  map_add' S T := by
    ext x
    rfl
  map_smul' c T := by
    ext x
    rfl

theorem complexValueAtOne_apply (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (principalSeriesRep ℂ n χ) d τ) (x : Fin d → ℂ) :
    complexValueAtOne χ d τ T x =
      ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) x :
        Langlands.GeneralLinear n ℂ → ℂ) 1 :=
  rfl

/-- The value of `T x` at `k ∈ U(n)` is the value at the identity of `T (τ(k) x)`. -/
theorem complexIntertwiner_apply_unitary (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (principalSeriesRep ℂ n χ) d τ) (x : Fin d → ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) x :
        Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) =
      complexValueAtOne χ d τ T (τ k *ᵥ x) := by
  rw [complexValueAtOne_apply, T.2 k x, principalSeriesRep_apply_coe]
  change _ = ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions (principalSeries ℂ n χ)
    (unitaryCompact ℂ n)) x : Langlands.GeneralLinear n ℂ → ℂ) (1 * Unitary.toUnits k)
  rw [one_mul]

/-- A `U(n)`-intertwiner into the `U(n)`-finite functions of a complex principal series is
determined by its values at the identity. -/
theorem complexValueAtOne_injective (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Function.Injective (complexValueAtOne χ d τ) := by
  intro S T hST
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_principalSeries_of_eqOn (sub_mem
    (((S : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
      x).2.1)
    (((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
      x).2.1)) ?_
  intro k hk
  have hk' : (Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℂ) : Langlands.GeneralLinear n ℂ) = k :=
    Units.ext rfl
  rw [Pi.sub_apply, ← hk', complexIntertwiner_apply_unitary, complexIntertwiner_apply_unitary,
    hST, sub_self]

/-- The `U(n)`-finite functions of a complex principal series form an admissible
representation of `U(n)`: the intertwiners from a matrix representation of degree `d` form a
space of dimension at most `d`. -/
theorem isAdmissibleGKModule_principalSeriesRep :
    IsAdmissibleGKModule (principalSeriesRep ℂ n χ) := by
  intro d τ _
  exact Module.Finite.of_injective _ (complexValueAtOne_injective χ d τ)

end Admissible

/-! ## The integration pairing -/

section Pairing

variable {n : ℕ} {χ χ' : ℕ → ℂˣ → ℂ}

variable (χ χ') in
/-- The integration pairing is invariant under the action of `U(n)` by right translation. -/
theorem integralPairing_principalSeriesRep (k : Matrix.unitaryGroup (Fin n) ℂ)
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (h : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) :
    integralPairing n χ χ' (principalSeriesRep ℂ n χ k f) (principalSeriesRep ℂ n χ' k h) =
      integralPairing n χ χ' f h :=
  integralPairing_rightTranslation χ χ' ⟨Unitary.toUnits k, k.2⟩ f h
    (principalSeriesRep ℂ n χ k f).2 (principalSeriesRep ℂ n χ' k h).2

/-- For pointwise inverse characters, the integration pairing is invariant under right
derivatives. -/
theorem integralPairing_principalSeriesLie (hχ : ∀ i z, χ i z * χ' i z = 1)
    (X : Matrix (Fin n) (Fin n) ℂ)
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (h : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) :
    integralPairing n χ χ' (principalSeriesLie ℂ n χ (1 ⊗ₜ X) f) h +
      integralPairing n χ χ' f (principalSeriesLie ℂ n χ' (1 ⊗ₜ X) h) = 0 := by
  rw [integralPairing_apply, integralPairing_apply, principalSeriesLie_one_tmul_apply_coe,
    principalSeriesLie_one_tmul_apply_coe]
  exact integral_rightDerivative_mul_add_eq_zero (unitaryHaar n) χ χ' hχ
    (Submodule.mem_inf.mp f.2).1 (Submodule.mem_inf.mp h.2).1 X

/-- Nondegeneracy of the integration pairing in its second argument. -/
theorem exists_integralPairing_ne_zero_left (hχ : ∀ i z, χ i z * χ' i z = 1) {s : ℕ → ℝ}
    (hs : ∀ i (z : ℂˣ), Complex.normSq (χ i z) = Complex.normSq (z : ℂ) ^ s i)
    (h : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) (h0 : h ≠ 0) :
    ∃ f, integralPairing n χ χ' f h ≠ 0 :=
  exists_integral_mul_ne_zero hχ hs h h0

/-- Nondegeneracy of the integration pairing in its first argument: the integrand is
symmetric, so this is nondegeneracy in the second argument with the roles of `χ` and `χ'`
exchanged. -/
theorem exists_integralPairing_ne_zero_right (hχ : ∀ i z, χ i z * χ' i z = 1) {s : ℕ → ℝ}
    (hs : ∀ i (z : ℂˣ), Complex.normSq (χ' i z) = Complex.normSq (z : ℂ) ^ s i)
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) (f0 : f ≠ 0) :
    ∃ h, integralPairing n χ χ' f h ≠ 0 := by
  obtain ⟨h, hh⟩ := exists_integral_mul_ne_zero (χ := χ') (χ' := χ)
    (fun i z => by rw [mul_comm]; exact hχ i z) hs f f0
  refine ⟨h, fun hzero => hh ?_⟩
  rw [← hzero, integralPairing_apply]
  congr 1
  funext k
  exact mul_comm _ _

end Pairing

/-! ## Finite vectors of the dual -/

section FiniteDual

variable {K : Type*} [Group K] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ρ : Representation ℂ K V} {σ : Representation ℂ K W}

/-- An equivariant linear map into the dual carries finite vectors to finite vectors of the
dual representation. -/
theorem isFiniteVector_dual_of_equivariant (L : W →ₗ[ℂ] Module.Dual ℂ V)
    (hL : ∀ (k : K) (w : W), L (σ k w) = ρ.dual k (L w)) {w : W}
    (hw : FiniteVectors.IsFiniteVector σ w) : FiniteVectors.IsFiniteVector ρ.dual (L w) := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan σ w) := hw
  change Module.Finite ℂ (FiniteVectors.orbitSpan ρ.dual (L w))
  refine Submodule.finiteDimensional_of_le (S₂ := (FiniteVectors.orbitSpan σ w).map L) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨σ k w, FiniteVectors.action_mem_orbitSpan σ k w, hL k w⟩

end FiniteDual

/-! ## Intertwining maps -/

section Intertwining

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ds : List ComplexCharacterData}
  {A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V}

/-- An intertwining map carries `complexStandardRep n ds k` to `ρ k`. -/
theorem map_complexStandardRep (hA : IsComplexStandardIntertwining n ρ π ds A)
    (k : Matrix.unitaryGroup (Fin n) ℂ)
    (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    A (complexStandardRep n ds k f) = ρ k (A f) := by
  obtain ⟨hf, h⟩ := hA.1 ⟨Unitary.toUnits k, k.2⟩ f
  exact (congrArg A (Subtype.ext rfl)).trans h

/-- An intertwining map carries `complexStandardLie n ds (1 ⊗ X)` to `π (1 ⊗ X)`. -/
theorem map_complexStandardLie (hA : IsComplexStandardIntertwining n ρ π ds A)
    (X : Matrix (Fin n) (Fin n) ℂ)
    (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) :
    A (complexStandardLie n ds (1 ⊗ₜ X) f) = π (1 ⊗ₜ X) (A f) := by
  obtain ⟨hf, h⟩ := hA.2 X f
  refine (congrArg A (Subtype.ext ?_)).trans h
  exact principalSeriesLie_one_tmul_apply_coe ℂ n _ X f

/-- A linear map carrying `complexStandardRep n ds k` to `ρ k` and
`complexStandardLie n ds (1 ⊗ X)` to `π (1 ⊗ X)` is an intertwining map. -/
theorem isComplexStandardIntertwining_of
    (hK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ)
      (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      A (complexStandardRep n ds k f) = ρ k (A f))
    (hX : ∀ (X : Matrix (Fin n) (Fin n) ℂ)
      (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      A (complexStandardLie n ds (1 ⊗ₜ X) f) = π (1 ⊗ₜ X) (A f)) :
    IsComplexStandardIntertwining n ρ π ds A := by
  refine ⟨fun k f =>
      ⟨rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 k.2, ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X, ?_⟩⟩
  · rw [← hK]
    congr 1
    apply Subtype.ext
    rw [principalSeriesRep_apply_coe]
    have hk : (Unitary.toUnits
        (⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ :
          Matrix.unitaryGroup (Fin n) ℂ) : Langlands.GeneralLinear n ℂ) =
        (k : Langlands.GeneralLinear n ℂ) :=
      Units.ext rfl
    rw [hk]
  · rw [← hX]
    congr 1
    apply Subtype.ext
    rw [principalSeriesLie_one_tmul_apply_coe]

end Intertwining

/-! ## The transpose -/

/-- Transposition for arbitrary lists: if the position characters of `d'` and `c'` are
pointwise inverse to those of `d` and `c`, a nonzero intertwining map `X(d) → X(c)` has a
nonzero transpose `X(c') → X(d')` under the integration pairings. -/
theorem exists_transpose (n : ℕ) (d c d' c' : List ComplexCharacterData)
    (hd : ∀ i z, complexPositionCharacter d' i z * complexPositionCharacter d i z = 1)
    (hc : ∀ i z, complexPositionCharacter c' i z * complexPositionCharacter c i z = 1)
    (T : kFiniteFunctions (complexStandardModule n d) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n c) (unitaryCompact ℂ n))
    (hT0 : T ≠ 0)
    (hT : IsComplexStandardIntertwining n (complexStandardRep n c) (complexStandardLie n c) d T) :
    ∃ T' : kFiniteFunctions (complexStandardModule n c') (unitaryCompact ℂ n) →ₗ[ℂ]
        kFiniteFunctions (complexStandardModule n d') (unitaryCompact ℂ n),
      T' ≠ 0 ∧
        IsComplexStandardIntertwining n (complexStandardRep n d') (complexStandardLie n d') c'
          T' := by
  -- The two pairings `⟨·, ·⟩_c : X(c') × X(c) → ℂ` and `⟨·, ·⟩_d : X(d') × X(d) → ℂ`.
  set Qc := integralPairing n (complexPositionCharacter c') (complexPositionCharacter c)
    with hQc
  set Qd := integralPairing n (complexPositionCharacter d') (complexPositionCharacter d)
    with hQd
  obtain ⟨sd, hsd⟩ := exists_normSq_complexPositionCharacter d
  obtain ⟨sd', hsd'⟩ := exists_normSq_complexPositionCharacter d'
  obtain ⟨sc', hsc'⟩ := exists_normSq_complexPositionCharacter c'
  have hTK := map_complexStandardRep hT
  have hTX := map_complexStandardLie hT
  -- The functionals `h ↦ ⟨f, T h⟩_c` on `X(d)`.
  set Λ := Qc.compl₂ T with hΛ
  have hΛapp : ∀ f h, Λ f h = Qc f (T h) := fun f h => rfl
  -- Equivariance of `g ↦ ⟨g, ·⟩_d` and of `Λ` for the dual action on functionals on `X(d)`.
  have hQdK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) g,
      Qd (complexStandardRep n d' k g) = (complexStandardRep n d).dual k (Qd g) := by
    intro k g
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply]
    have e := integralPairing_principalSeriesRep (complexPositionCharacter d')
      (complexPositionCharacter d) k g (complexStandardRep n d k⁻¹ h)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have hΛK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
      Λ (complexStandardRep n c' k f) = (complexStandardRep n d).dual k (Λ f) := by
    intro k f
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply, hΛapp, hΛapp, hTK]
    have e := integralPairing_principalSeriesRep (complexPositionCharacter c')
      (complexPositionCharacter c) k f (complexStandardRep n c k⁻¹ (T h))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  -- Representability of `U(n)`-finite functionals on `X(d)`.
  have hgkd := isComplexGKModule_complexStandardModule n d
  have hgkd' := isComplexGKModule_complexStandardModule n d'
  have hgkc' := isComplexGKModule_complexStandardModule n c'
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℂ]
      (complexStandardRep n d).asModule :=
    KFiniteDual.isSemisimpleModule hgkd.1 hgkd.2.1
  have hblock := KFiniteDual.finiteDimensional_block hgkd.1 hgkd.2.1
    (isAdmissibleGKModule_principalSeriesRep (n := n) (complexPositionCharacter d))
  let W' : Subrepresentation (complexStandardRep n d).dual :=
    { toSubmodule := LinearMap.range Qd
      apply_mem_toSubmodule := by
        rintro k _ ⟨g, rfl⟩
        exact ⟨complexStandardRep n d' k g, hQdK k g⟩ }
  have hW' : ∀ w ∈ W', FiniteVectors.IsFiniteVector (complexStandardRep n d).dual w := by
    rintro _ ⟨g, rfl⟩
    exact isFiniteVector_dual_of_equivariant Qd hQdK (hgkd'.1 g)
  have hsep : ∀ h, (∀ w ∈ W', w h = 0) → h = 0 := by
    intro h hh
    by_contra hne
    obtain ⟨g, hg⟩ := exists_integralPairing_ne_zero_left hd hsd' h hne
    exact hg (hh _ ⟨g, rfl⟩)
  have hrange : ∀ f, Λ f ∈ LinearMap.range Qd := fun f =>
    KFiniteDual.mem_of_separating hblock W' hW' hsep
      (isFiniteVector_dual_of_equivariant Λ hΛK (hgkc'.1 f))
  have hQdinj : Function.Injective Qd := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    by_contra hne
    obtain ⟨h, hh⟩ := exists_integralPairing_ne_zero_right hd hsd g hne
    exact hh (by rw [hg, LinearMap.zero_apply])
  -- The transpose `T'`, with `⟨T' f, h⟩_d = ⟨f, T h⟩_c`.
  set T' : kFiniteFunctions (complexStandardModule n c') (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n d') (unitaryCompact ℂ n) :=
    (LinearEquiv.ofInjective Qd hQdinj).symm.toLinearMap ∘ₗ
      Λ.codRestrict (LinearMap.range Qd) hrange with hT'def
  have hT' : ∀ f h, Qd (T' f) h = Qc f (T h) := by
    intro f h
    have e := congrArg Subtype.val
      ((LinearEquiv.ofInjective Qd hQdinj).apply_symm_apply
        (Λ.codRestrict (LinearMap.range Qd) hrange f))
    rw [LinearEquiv.ofInjective_apply] at e
    exact congrArg (fun ℓ => ℓ h) e
  have hext : ∀ x y, (∀ h, Qd x h = Qd y h) → x = y := fun x y hxy =>
    hQdinj (LinearMap.ext hxy)
  refine ⟨T', ?_, isComplexStandardIntertwining_of ?_ ?_⟩
  · -- `T' ≠ 0`.
    intro hT'0
    obtain ⟨h, hh⟩ : ∃ h, T h ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hT0 (LinearMap.ext hcon)
    obtain ⟨f, hf⟩ := exists_integralPairing_ne_zero_left hc hsc' (T h) hh
    apply hf
    rw [← hT', hT'0, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  · -- Equivariance for `U(n)`.
    intro k f
    apply hext
    intro h
    obtain ⟨h₀, rfl⟩ : ∃ h₀, complexStandardRep n d k h₀ = h :=
      ⟨complexStandardRep n d k⁻¹ h, by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    rw [hT', hTK, integralPairing_principalSeriesRep, integralPairing_principalSeriesRep, hT']
  · -- Equivariance for `𝔤𝔩_n(ℂ)`.
    intro X f
    apply hext
    intro h
    have h1 := integralPairing_principalSeriesLie hc X f (T h)
    have h2 := integralPairing_principalSeriesLie hd X (T' f) h
    rw [← hTX] at h1
    rw [hT'] at h2 ⊢
    linear_combination h1 - h2

/-- Proof of `ComplexStandardHomTransposeStatement`: apply `exists_transpose` with the lists
of pointwise inverse characters. -/
theorem complexStandardHomTranspose : ComplexStandardHomTransposeStatement := by
  intro n d c T hT0 hT
  have hinv : ∀ (e : Fin n → ComplexCharacterData) (i : ℕ) (z : ℂˣ),
      complexPositionCharacter (List.ofFn fun j => complexCharacterDataInv (e j)) i z *
        complexPositionCharacter (List.ofFn e) i z = 1 := by
    intro e i z
    have h := complexPositionCharacter_map_inv_mul (List.ofFn e) i z
    rwa [List.map_ofFn] at h
  exact exists_transpose n _ _ _ _ (hinv d) (hinv c) T hT0 hT

end Langlands.Archimedean.ComplexStandardHomTransposeProof
