import Langlands.Representation.Unramified.PairedHeckeScalars
import Langlands.Representation.Unitary.Basic

/-!
# Spherical spectra of unitarizable representations are closed under `α ↦ conj(α)⁻¹`

For a smooth representation of `GL_(r+1)(F)` with an invariant positive definite Hermitian
form and a nonzero spherical vector on which the standard Hecke elements act by the
standard Hecke scalars of a spectrum `s`, the complex conjugate of `s` is the inverse of
`s`: `conjSpectrum s = s.map (·⁻¹)`.

This is the Hermitian analogue of `PairedHecke.scalar_adjoint` and
`PairedHecke.eq_map_inv_of_pairing` (Library module
`Langlands.Representation.Unramified.PairedHeckeScalars`): an invariant Hermitian form pairs
the representation with itself conjugate-linearly, so the adjoint relation of the standard
Hecke scalars holds with the complex conjugate scalars on one side.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure GeneralLinear.Iwasawa MinusculeCosets

universe uF uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

/-- The complex conjugate of a spectrum. -/
def conjSpectrum {n : ℕ} (s : Eigenvalues n) : Eigenvalues n :=
  s.map (Units.map (starRingEnd ℂ).toMonoidHom)

theorem coe_conjSpectrum {n : ℕ} (s : Eigenvalues n) :
    ((conjSpectrum s : Eigenvalues n) : Multiset ℂˣ) =
      (s : Multiset ℂˣ).map (Units.map (starRingEnd ℂ).toMonoidHom) :=
  Sym.coe_map _ _

theorem powerTrace_conjSpectrum {n : ℕ} (s : Eigenvalues n) (k : ℕ) :
    (conjSpectrum s).powerTrace k = starRingEnd ℂ (s.powerTrace k) := by
  rw [Eigenvalues.powerTrace, Eigenvalues.powerTrace, coe_conjSpectrum, Multiset.map_map,
    map_multiset_sum, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro z _
  simp

theorem eulerPolynomial_conjSpectrum {n : ℕ} (s : Eigenvalues n) :
    Eigenvalues.eulerPolynomial (conjSpectrum s) =
      (Eigenvalues.eulerPolynomial s).map (starRingEnd ℂ) := by
  rw [Eigenvalues.eulerPolynomial, Eigenvalues.eulerPolynomial, Polynomial.map_multiset_prod,
    coe_conjSpectrum, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro z _
  simp [Polynomial.map_sub, Polynomial.map_mul]

theorem standardHeckeScalar_conjSpectrum {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
    (s : Eigenvalues (r + 1)) (i : Fin (r + 2)) :
    standardHeckeScalar F (conjSpectrum s) i = starRingEnd ℂ (standardHeckeScalar F s i) := by
  simp [standardHeckeScalar, elementaryCoefficient, eulerPolynomial_conjSpectrum,
    Polynomial.coeff_map, Complex.conj_ofReal]

namespace PairedHecke

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The linear functional `y ↦ ⟪a, y⟫` of an invariant positive form. -/
def formRight {G : Type*} [Monoid G] {ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ)
    (a : V) : V →ₗ[ℂ] ℂ where
  toFun y := b.inner a y
  map_add' y z := by
    let c' : PreInnerProductSpace.Core ℂ V := b.toInnerProductCore.toCore
    let _ : Inner ℂ V := InnerProductSpace.Core.toPreInner'
    exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) a y z
  map_smul' c y := by
    let c' : PreInnerProductSpace.Core ℂ V := b.toInnerProductCore.toCore
    let _ : Inner ℂ V := InnerProductSpace.Core.toPreInner'
    change b.inner a (c • y) = c * b.inner a y
    exact InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) a y

theorem formRight_apply {G : Type*} [Monoid G] {ρ : Representation ℂ G V}
    (b : InvariantPositiveForm ρ) (a y : V) : formRight b a y = b.inner a y := rfl

theorem conj_standardHeckeElement (j : Fin (r + 2)) (g : GeneralLinear (r + 1) F.Carrier) :
    starRingEnd ℂ (standardHeckeElement F r j g) = standardHeckeElement F r j g := by
  classical
  rw [standardHeckeElement_apply]
  by_cases h : g ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
      (standardDiagonal F r j)
  · rw [Set.indicator_of_mem h, map_one]
  · rw [Set.indicator_of_notMem h, map_zero]

theorem inner_self_ne_zero {G : Type*} [Monoid G] {ρ : Representation ℂ G V}
    (b : InvariantPositiveForm ρ) {v : V} (hv : v ≠ 0) : b.inner v v ≠ 0 := by
  intro h
  exact hv (b.definite v h)

theorem conj_inner_self {G : Type*} [Monoid G] {ρ : Representation ℂ G V}
    (b : InvariantPositiveForm ρ) (v : V) : starRingEnd ℂ (b.inner v v) = b.inner v v :=
  b.conj_inner_symm v v

/-- **Hermitian adjointness of the standard Hecke scalars.** If a nonzero spherical vector of
a representation with an invariant positive form is an eigenvector of the standard Hecke
elements with scalars `l`, then `conj (l j) = conj (l n) * l (n - j)`. -/
theorem scalar_conj_adjoint (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (b : InvariantPositiveForm ρ)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) (l : Fin (r + 2) → ℂ)
    (ha : ∀ i, corner F ρ hρ (standardHeckeElement F r i) a = l i • a)
    (ha0 : (a : V) ≠ 0) (j : Fin (r + 2)) :
    starRingEnd ℂ (l j) = starRingEnd ℂ (l (Fin.last (r + 1))) * l j.rev := by
  set t := standardDiagonal F r (Fin.last (r + 1)) with ht
  set θ := sphericalInverseTranspose F r
  let K := sphericalOpenSubgroup F r
  let c : GeneralLinear (r + 1) F.Carrier → ℂ := fun g => b.inner a (ρ g a)
  have hfixa : ∀ k : K, ρ k a = a := fun k => a.property ⟨k, k.2⟩
  have hc : ∀ (k₁ k₂ : K) g, c (k₁ * g * k₂) = c g := by
    intro k₁ k₂ g
    change b.inner a (ρ (k₁ * g * k₂) a) = b.inner a (ρ g a)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfixa k₂]
    calc b.inner a (ρ k₁ (ρ g a)) = b.inner (ρ k₁ a) (ρ k₁ (ρ g a)) := by rw [hfixa k₁]
      _ = b.inner a (ρ g a) := b.invariant _ _ _
  have hta : ρ t a = l (Fin.last (r + 1)) • (a : V) := by
    rw [← corner_last F ρ hρ, ha]
    rfl
  have hct : ∀ g, c g = starRingEnd ℂ (l (Fin.last (r + 1))) * c (t * g) := by
    intro g
    change b.inner a (ρ g a) = _ * b.inner a (ρ (t * g) a)
    rw [← b.invariant t a (ρ g a), hta, b.smul_left, map_mul, Module.End.mul_apply]
  have hsym : ∀ u, standardHeckeElement F r j (θ u) * c (θ u)⁻¹ =
      standardHeckeElement F r j u⁻¹ * c u := by
    intro u
    obtain ⟨k₁, k₂, hu⟩ := sphericalInverseTranspose_mem_doubleCoset_inv F r u
    rw [hu, Hecke.HeckeAlgebra.Corner.apply_mul_mul]
    congr 1
    have e : ((k₁ : GeneralLinear (r + 1) F.Carrier) * u⁻¹ * k₂)⁻¹ =
        (k₂⁻¹ : K) * u * (k₁⁻¹ : K) := by
      simp [mul_assoc]
    rw [e, hc]
  have hab : b.inner a a ≠ 0 := inner_self_ne_zero b ha0
  have h1 : starRingEnd ℂ (l j) * b.inner a a =
      ∫ g, standardHeckeElement F r j g * c g⁻¹ ∂(sphericalHaar F r) := by
    have h := functional_corner F ρ hρ (standardHeckeElement F r j) a (formRight b a)
    rw [ha, Submodule.coe_smul, map_smul, smul_eq_mul] at h
    have h' := congrArg (starRingEnd ℂ) h
    rw [map_mul, formRight_apply, conj_inner_self, ← integral_conj] at h'
    rw [h']
    congr 1
    funext g
    rw [map_mul, conj_standardHeckeElement, formRight_apply, b.conj_inner_symm]
    congr 1
    change b.inner (ρ g a) a = b.inner a (ρ g⁻¹ a)
    calc b.inner (ρ g a) a = b.inner (ρ g⁻¹ (ρ g a)) (ρ g⁻¹ a) := (b.invariant _ _ _).symm
      _ = b.inner a (ρ g⁻¹ a) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h2 : ∫ g, standardHeckeElement F r j.rev g * c g ∂(sphericalHaar F r) =
      l j.rev * b.inner a a := by
    have h := functional_corner F ρ hρ (standardHeckeElement F r j.rev) a (formRight b a)
    rw [ha, Submodule.coe_smul, map_smul, smul_eq_mul] at h
    exact h.symm
  have key : starRingEnd ℂ (l j) * b.inner a a =
      starRingEnd ℂ (l (Fin.last (r + 1))) * l j.rev * b.inner a a := by
    calc starRingEnd ℂ (l j) * b.inner a a
        = ∫ g, standardHeckeElement F r j g * c g⁻¹ ∂(sphericalHaar F r) := h1
      _ = ∫ u, standardHeckeElement F r j (θ u) * c (θ u)⁻¹ ∂(sphericalHaar F r) :=
          ((sphericalHaar_measurePreserving_inverseTranspose F r).integral_comp
            θ.toHomeomorph.measurableEmbedding
            (fun g => standardHeckeElement F r j g * c g⁻¹)).symm
      _ = ∫ u, starRingEnd ℂ (l (Fin.last (r + 1))) *
            (standardHeckeElement F r j.rev (t * u) * c (t * u)) ∂(sphericalHaar F r) := by
          congr 1
          funext u
          rw [hsym, standardHeckeElement_inv, ← ht, hct u]
          ring
      _ = starRingEnd ℂ (l (Fin.last (r + 1))) * l j.rev * b.inner a a := by
          rw [integral_const_mul, integral_mul_left_eq_self
            (fun u => standardHeckeElement F r j.rev u * c u) t, h2, mul_assoc]
  exact mul_right_cancel₀ hab key

/-- **The conjugate spectrum is the inverse spectrum.** A nonzero spherical eigenvector of a
representation with an invariant positive form, with the standard Hecke scalars of `s`,
forces `conj s = s⁻¹`. -/
theorem conjSpectrum_eq_map_inv_of_form
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsSmooth ρ)
    (b : InvariantPositiveForm ρ) (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup)
    (s : Eigenvalues (r + 1))
    (ha : ∀ i, corner F ρ hρ (standardHeckeElement F r i) a = standardHeckeScalar F s i • a)
    (ha0 : (a : V) ≠ 0) :
    conjSpectrum s = s.map fun z => z⁻¹ :=
  eq_map_inv_of_standardHeckeScalar F s (conjSpectrum s) fun j => by
    rw [standardHeckeScalar_conjSpectrum, standardHeckeScalar_conjSpectrum]
    exact scalar_conj_adjoint F ρ hρ b a _ ha ha0 j

end PairedHecke

/-- **Unitarizable spherical spectra.** If a unitarizable automorphic object has spherical
Hecke spectrum `s`, then `conj s = s⁻¹`: the Satake parameters are closed under
`α ↦ conj(α)⁻¹`. -/
theorem conjSpectrum_eq_map_inv_of_hasSphericalHeckeSpectrum {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) {r : ℕ} (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (hU : IsUnitarizable A.obj.representation) {s : Eigenvalues (r + 1)}
    (hs : HasSphericalHeckeSpectrum F A s) :
    conjSpectrum s = s.map fun z => z⁻¹ := by
  obtain ⟨b⟩ := hU
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs.1
  let w : fixedVectors A.obj.representation (sphericalSubgroup F r) := ⟨x, hx⟩
  exact PairedHecke.conjSpectrum_eq_map_inv_of_form F A.obj.representation A.obj.isSmooth b w s
    (fun i => hs.2 i w) hx0

end Langlands.Unramified
