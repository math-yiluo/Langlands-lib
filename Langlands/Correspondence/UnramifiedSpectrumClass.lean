import Langlands.Correspondence.CharacterSumConverse
import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-!
# Unramified parameter classes of spectra

Every unramified parameter class of rank `r + 1` is the character-sum class of unramified
characters, and is determined by the unordered spectrum of geometric Frobenius
eigenvalues. `unramifiedSpectrumClass F s` is the unramified class of a spectrum `s`; its
standard Euler polynomial is `Eigenvalues.eulerPolynomial s`.
-/

noncomputable section

universe uF uP

open Polynomial

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance unramifiedSpectrumClassFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable {F}

/-- Every unramified parameter class of rank `r + 1` is the unramified character-sum
class of some `r + 1` units. -/
theorem exists_eq_unramifiedCharacterSumClass {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsUnramifiedParameterClass F D) :
    ∃ c : Fin (r + 1) → ℂˣ, D = unramifiedCharacterSumClass.{uF, uP} F c := by
  classical
  set Φ := Weil.Local.localGeometricFrobenius F
  obtain ⟨d, hd⟩ := D
  obtain ⟨a, rfl⟩ := Quotient.exists_rep d
  have hfa : parameterForget F ⟨Quotient.mk _ a, hd⟩ =
      WeilDeligneRepresentation.classOf a.val := rfl
  obtain ⟨B, hB, hBc⟩ := hD
  rw [hfa] at hBc
  obtain ⟨fB⟩ := (WeilDeligneRepresentation.classOf_eq_iff _ _).mp hBc
  have hN : a.val.monodromy = 0 :=
    WeilDeligneRepresentation.monodromy_eq_zero_of_equiv fB rfl
  have hI : ∀ i : Weil.Local.localInertia F, a.val.representation i = 1 :=
    FiniteRepresentation.isUnramified_of_equiv fB.representationEquiv hB
  have hS : Module.End.IsSemisimple (a.val.representation Φ) := by
    refine a.property.2 Φ ?_
    change Multiplicative.toAdd (Weil.Local.localDegree F Φ) ≠ 0
    rw [Weil.Local.localGeometricFrobenius_degree]
    simp
  obtain ⟨b, μ, hb⟩ := LocalFactor.exists_basis_apply_eq_smul_of_isSemisimple hS
  have hμ0 : ∀ j, μ j ≠ 0 := by
    intro j h0
    have hj := hb j
    rw [h0, zero_smul] at hj
    apply b.ne_zero j
    have := congrArg (a.val.representation Φ⁻¹) hj
    rwa [Representation.inv_self_apply, map_zero] at this
  have hrank : Module.finrank ℂ a.val = r + 1 := hd
  let e := finCongr hrank
  let c : Fin (r + 1) → ℂˣ := fun i => Units.mk0 (μ (e.symm i)) (hμ0 _)
  have hb' : ∀ i, a.val.representation Φ (b.reindex e i) = (c i : ℂ) • b.reindex e i := by
    intro i
    rw [Module.Basis.reindex_apply, hb]
    rfl
  obtain ⟨f⟩ := nonempty_equiv_characterSumPair hN hI c (b.reindex e) hb'
  refine ⟨c, ?_⟩
  apply parameterForget_injective
  rw [hfa, unramifiedCharacterSumClass, parameterForget_characterSumClass]
  exact ((WeilDeligneRepresentation.classOf_eq_iff _ _).mpr ⟨f⟩).symm

variable (F) in
/-- The unramified parameter class of rank `r + 1` whose geometric Frobenius eigenvalues,
with multiplicities, are the spectrum `s`: the unramified character-sum class of a chosen
ordering of `s`. -/
def unramifiedSpectrumClass {r : ℕ} (s : Unramified.Eigenvalues (r + 1)) :
    WeilDeligneClass.{uF, uP} F r.succPNat :=
  unramifiedCharacterSumClass.{uF, uP} F
    (Classical.choose (Unramified.Eigenvalues.ofTuple_surjective (r + 1) s))

/-- The standard Euler polynomial of `unramifiedSpectrumClass F s` is the Euler
polynomial of the spectrum `s`. -/
theorem parameterEulerPolynomial_unramifiedSpectrumClass {r : ℕ}
    (s : Unramified.Eigenvalues (r + 1)) :
    parameterEulerPolynomial F (unramifiedSpectrumClass.{uF, uP} F s) =
      Unramified.Eigenvalues.eulerPolynomial s := by
  have hs := Classical.choose_spec (Unramified.Eigenvalues.ofTuple_surjective (r + 1) s)
  rw [unramifiedSpectrumClass, parameterEulerPolynomial_unramifiedCharacterSumClass]
  conv_rhs => rw [← hs]
  rw [Unramified.Eigenvalues.eulerPolynomial_ofTuple]

/-- The unramified character-sum class of an ordered tuple is the unramified class of its
unordered spectrum. -/
theorem unramifiedCharacterSumClass_eq_unramifiedSpectrumClass {r : ℕ}
    (c : Fin (r + 1) → ℂˣ) :
    unramifiedCharacterSumClass.{uF, uP} F c =
      unramifiedSpectrumClass.{uF, uP} F (Unramified.Eigenvalues.ofTuple c) := by
  symm
  rw [← parameterEulerPolynomial_eq_prod_iff, parameterEulerPolynomial_unramifiedSpectrumClass,
    Unramified.Eigenvalues.eulerPolynomial_ofTuple]

/-- A parameter class has standard Euler polynomial `Eigenvalues.eulerPolynomial s`
exactly when it is the unramified class of the spectrum `s`. -/
theorem parameterEulerPolynomial_eq_eulerPolynomial_iff {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (s : Unramified.Eigenvalues (r + 1)) :
    parameterEulerPolynomial F D = Unramified.Eigenvalues.eulerPolynomial s ↔
      D = unramifiedSpectrumClass.{uF, uP} F s := by
  obtain ⟨c, rfl⟩ := Unramified.Eigenvalues.ofTuple_surjective (r + 1) s
  rw [Unramified.Eigenvalues.eulerPolynomial_ofTuple, parameterEulerPolynomial_eq_prod_iff,
    unramifiedCharacterSumClass_eq_unramifiedSpectrumClass]

/-- Distinct spectra give distinct unramified parameter classes. -/
theorem unramifiedSpectrumClass_injective (r : ℕ) :
    Function.Injective (unramifiedSpectrumClass.{uF, uP} F :
      Unramified.Eigenvalues (r + 1) → WeilDeligneClass.{uF, uP} F r.succPNat) := by
  intro s t h
  apply Unramified.Eigenvalues.eulerPolynomial_injective
  have hE := congrArg (parameterEulerPolynomial F) h
  rwa [parameterEulerPolynomial_unramifiedSpectrumClass,
    parameterEulerPolynomial_unramifiedSpectrumClass] at hE

theorem unramifiedSpectrumClass_inj {r : ℕ} {s t : Unramified.Eigenvalues (r + 1)} :
    unramifiedSpectrumClass.{uF, uP} F s = unramifiedSpectrumClass.{uF, uP} F t ↔ s = t :=
  (unramifiedSpectrumClass_injective r).eq_iff

/-- Two unramified character-sum classes agree exactly when the tuples have the same
unordered spectrum. -/
theorem unramifiedCharacterSumClass_eq_iff {r : ℕ} (c c' : Fin (r + 1) → ℂˣ) :
    unramifiedCharacterSumClass.{uF, uP} F c = unramifiedCharacterSumClass.{uF, uP} F c' ↔
      Unramified.Eigenvalues.ofTuple c = Unramified.Eigenvalues.ofTuple c' := by
  rw [unramifiedCharacterSumClass_eq_unramifiedSpectrumClass,
    unramifiedCharacterSumClass_eq_unramifiedSpectrumClass, unramifiedSpectrumClass_inj]

theorem isUnramifiedParameterClass_unramifiedSpectrumClass {r : ℕ}
    (s : Unramified.Eigenvalues (r + 1)) :
    IsUnramifiedParameterClass F (unramifiedSpectrumClass.{uF, uP} F s) :=
  isUnramifiedParameterClass_unramifiedCharacterSumClass _

/-- A parameter class of rank `r + 1` is unramified exactly when it is the unramified
class of some spectrum. -/
theorem isUnramifiedParameterClass_iff_exists_unramifiedSpectrumClass {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} :
    IsUnramifiedParameterClass F D ↔
      ∃ s : Unramified.Eigenvalues (r + 1), D = unramifiedSpectrumClass.{uF, uP} F s := by
  refine ⟨fun hD => ?_, fun ⟨s, hs⟩ => hs ▸ isUnramifiedParameterClass_unramifiedSpectrumClass s⟩
  obtain ⟨c, hc⟩ := exists_eq_unramifiedCharacterSumClass hD
  exact ⟨Unramified.Eigenvalues.ofTuple c,
    hc.trans (unramifiedCharacterSumClass_eq_unramifiedSpectrumClass c)⟩

/-- A parameter class of rank `r + 1` is unramified exactly when its standard Euler
polynomial is the Euler polynomial of some spectrum. -/
theorem isUnramifiedParameterClass_iff_exists_eulerPolynomial {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} :
    IsUnramifiedParameterClass F D ↔
      ∃ s : Unramified.Eigenvalues (r + 1),
        parameterEulerPolynomial F D = Unramified.Eigenvalues.eulerPolynomial s := by
  simp only [parameterEulerPolynomial_eq_eulerPolynomial_iff]
  exact isUnramifiedParameterClass_iff_exists_unramifiedSpectrumClass

/-- For a geometric candidate and unramified quasi-characters `χ_i`, the character-sum
parameter of `χ` is the unramified class of the uniformizer spectrum of `χ`. -/
theorem isCharacterSumParameter_iff_eq_unramifiedSpectrumClass {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} :
    IsCharacterSumParameter F e χ D ↔
      D = unramifiedSpectrumClass.{uF, uP} F (Unramified.characterSpectrum F χ) := by
  rw [isCharacterSumParameter_iff_parameterEulerPolynomial he hχ,
    parameterEulerPolynomial_eq_prod_iff, unramifiedCharacterSumClass_eq_unramifiedSpectrumClass]
  exact Iff.rfl

theorem isCharacterSumParameter_unramifiedSpectrumClass {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) :
    IsCharacterSumParameter F e χ
      (unramifiedSpectrumClass.{uF, uP} F (Unramified.characterSpectrum F χ)) :=
  (isCharacterSumParameter_iff_eq_unramifiedSpectrumClass he hχ).mpr rfl

/-- For a geometric candidate, the unramified character-sum class of `z` is the
character-sum parameter of the unramified characters with uniformizer values `z_i`. -/
theorem isCharacterSumParameter_characterTuple {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    IsCharacterSumParameter F e (Unramified.characterTuple F z)
      (unramifiedCharacterSumClass.{uF, uP} F z) := by
  rw [isCharacterSumParameter_iff_eq_unramifiedSpectrumClass he
    (Unramified.characterTuple_isUnramified F z), Unramified.characterSpectrum_characterTuple]
  exact unramifiedCharacterSumClass_eq_unramifiedSpectrumClass z

end Langlands.Correspondence
