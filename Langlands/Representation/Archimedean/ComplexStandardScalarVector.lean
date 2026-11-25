import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof
import Langlands.Representation.Archimedean.ComplexPermutationSwap
import Mathlib.Data.Fin.Tuple.Sort

/-! # A scalar vector in every complex standard module

Every `U(n)`-finite complex standard module `X(ds)` of `n` characters contains a nonzero vector
`f₀` that every `U(n)`-equivariant linear endomorphism maps to a multiple of itself
(`exists_isScalarVector`). For weights in nondecreasing order, `f₀` is the minor-monomial vector
of the Library (`complexLowestKTypeMultOne`). In general, the standard module is
`U(n)`-isomorphic to the one of the list sorted by weight (`permKMap`). See the paired Markdown.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexStandardScalarVector

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-- The `U(n)`-finite functions of the complex standard module of `ds`. -/
abbrev KF (n : ℕ) (ds : List ComplexCharacterData) :=
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

/-- `f₀` is a scalar vector of `X(ds)`: it is nonzero, and every `U(n)`-equivariant linear
endomorphism of `X(ds)` maps it to a multiple of itself. -/
def IsScalarVector (ds : List ComplexCharacterData) (f₀ : KF n ds) : Prop :=
  f₀ ≠ 0 ∧ ∀ E : KF n ds →ₗ[ℂ] KF n ds,
    (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds),
      E (complexStandardRep n ds k f) = complexStandardRep n ds k (E f)) →
    ∃ a : ℂ, E f₀ = a • f₀

open ComplexTemperedIrreducible ComplexStrictLanglandsQuotient in
/-- **Sorted weights.** If the weights of `ds` are nondecreasing, the minor-monomial vector is a
scalar vector. -/
theorem exists_isScalarVector_of_sorted (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (hsort : ds.Pairwise (fun d e => d.weight ≤ e.weight)) : ∃ f₀ : KF n ds, IsScalarVector ds f₀ := by
  have hw' : ∀ d ∈ untwist ds, d.weight = 0 := weight_untwist
  have hmono : ∀ i, i + 1 < n → complexPositionWeight ds i ≤ complexPositionWeight ds (i + 1) := by
    intro i hi
    rw [positionWeight_eq ds i (by omega), positionWeight_eq ds (i + 1) (by omega)]
    exact List.pairwise_iff_getElem.mp hsort i (i + 1) (by omega) (by omega) (by omega)
  obtain ⟨c, d, hcd⟩ := exists_minorWeight_eq n (complexPositionWeight ds) hmono
  have hchar : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ ComplexMinorProduct.minorWeight c d i *
        complexPositionCharacter (untwist ds) i z := by
    intro i z
    rw [hcd i]
    exact positionCharacter_untwist ds i (by rw [hlen]; exact i.isLt) z
  obtain ⟨T, hT, hT1⟩ := ComplexSphericalLieGroup.exists_spherical (n := n) hw'
  have hTK : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (T : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) = 1 := by
    intro κ
    have h := congrArg (fun f => kFiniteEval (complexStandardModule n (untwist ds)) 1 f) (hT κ)
    simp only [kFiniteEval_apply] at h hT1
    rw [← hT1, ← h, ComplexPermutation.complexStandardRep_apply_apply, one_mul]
  have hmin : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      ((ComplexMinorProduct.mulV c d hchar T : KF n ds) : Langlands.GeneralLinear n ℂ → ℂ)
          (Unitary.toUnits κ) =
        ComplexLowestKType.minorMonomial c d (κ : Matrix (Fin n) (Fin n) ℂ) := by
    intro κ
    rw [ComplexMinorProduct.mulV_coe]
    change ComplexMinorProduct.minorFun c d (Unitary.toUnits κ) *
      (T : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) = _
    rw [hTK, mul_one]
    rfl
  refine ⟨ComplexMinorProduct.mulV c d hchar T, fun h0 => ?_,
    fun E hE => complexLowestKTypeMultOne n ds c d _ hmin E hE⟩
  have h := hmin (ComplexMinorProduct.revUnitary n)
  rw [h0] at h
  exact ComplexMinorProduct.minorMonomial_revUnitary_ne_zero c d h.symm

/-- A scalar vector is carried to a scalar vector by a bijective `U(n)`-equivariant map. -/
theorem IsScalarVector.of_equiv {ds es : List ComplexCharacterData}
    (Φ : KF n ds ≃ₗ[ℂ] KF n es)
    (hΦ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds),
      Φ (complexStandardRep n ds k f) = complexStandardRep n es k (Φ f))
    {f₀ : KF n es} (h : IsScalarVector es f₀) : IsScalarVector ds (Φ.symm f₀) := by
  have hΦs : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n es),
      Φ.symm (complexStandardRep n es k f) = complexStandardRep n ds k (Φ.symm f) := by
    intro k f
    apply Φ.injective
    rw [LinearEquiv.apply_symm_apply, hΦ, LinearEquiv.apply_symm_apply]
  refine ⟨fun h0 => h.1 ?_, fun E hE => ?_⟩
  · rw [← Φ.apply_symm_apply f₀, h0, LinearEquiv.map_zero]
  · obtain ⟨a, ha⟩ := h.2 (Φ.toLinearMap ∘ₗ E ∘ₗ Φ.symm.toLinearMap) (fun k f => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΦs, hE, hΦ])
    refine ⟨a, Φ.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact ha

/-- **Every standard module of `n` characters has a scalar vector.** -/
theorem exists_isScalarVector (ds : List ComplexCharacterData) (hlen : ds.length = n) :
    ∃ f₀ : KF n ds, IsScalarVector ds f₀ := by
  set d : Fin n → ComplexCharacterData := fun j => ds.get (Fin.cast hlen.symm j) with hd_def
  have hd : List.ofFn d = ds := ComplexPermutation.ofFn_get_eq ds hlen
  set τ := Tuple.sort (fun j => (d j).weight) with hτ
  set e : Fin n → ComplexCharacterData := fun k => d (τ k) with he_def
  have hΦ : ∃ Φ : KF n ds →ₗ[ℂ] KF n (List.ofFn e),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds),
        Φ (complexStandardRep n ds k f) = complexStandardRep n (List.ofFn e) k (Φ f)) ∧
        Function.Injective Φ := by
    have h := (⟨ComplexPermutation.permKMap d τ.symm,
      ComplexPermutation.permKMap_equivariant d τ.symm,
      ComplexPermutation.permKMap_injective d τ.symm⟩ :
      ∃ Φ : KF n (List.ofFn d) →ₗ[ℂ] KF n (List.ofFn fun k => d (τ.symm.symm k)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (List.ofFn d)),
          Φ (complexStandardRep n (List.ofFn d) k f) =
            complexStandardRep n (List.ofFn fun k => d (τ.symm.symm k)) k (Φ f)) ∧
          Function.Injective Φ)
    rw [hd] at h
    exact h
  have h2 : (List.ofFn fun k => e (τ.symm k)) = ds := by
    rw [← hd]
    congr 1
    funext k
    simp only [he_def, Equiv.apply_symm_apply]
  have hΨ : ∃ Ψ : KF n (List.ofFn e) →ₗ[ℂ] KF n ds,
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (List.ofFn e)),
        Ψ (complexStandardRep n (List.ofFn e) k f) = complexStandardRep n ds k (Ψ f)) ∧
        Function.Injective Ψ := by
    have h := (⟨ComplexPermutation.permKMap e τ,
      ComplexPermutation.permKMap_equivariant e τ,
      ComplexPermutation.permKMap_injective e τ⟩ :
      ∃ Ψ : KF n (List.ofFn e) →ₗ[ℂ] KF n (List.ofFn fun k => e (τ.symm k)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (List.ofFn e)),
          Ψ (complexStandardRep n (List.ofFn e) k f) =
            complexStandardRep n (List.ofFn fun k => e (τ.symm k)) k (Ψ f)) ∧
          Function.Injective Ψ)
    rw [h2] at h
    exact h
  obtain ⟨Φ, hΦeq, hΦinj⟩ := hΦ
  obtain ⟨Ψ, hΨeq, hΨinj⟩ := hΨ
  have hΦsurj := ComplexPermutation.surjective_of_injective_of_kMap ds (List.ofFn e) Φ hΦeq
    hΦinj Ψ hΨeq hΨinj
  have hsort : (List.ofFn e).Pairwise (fun d e => d.weight ≤ e.weight) :=
    List.pairwise_ofFn.mpr fun i j hij => Tuple.monotone_sort (fun j => (d j).weight) hij.le
  obtain ⟨f₀, hf₀⟩ := exists_isScalarVector_of_sorted (List.ofFn e) (List.length_ofFn) hsort
  exact ⟨_, IsScalarVector.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩) hΦeq hf₀⟩

end Langlands.Archimedean.ComplexStandardScalarVector
