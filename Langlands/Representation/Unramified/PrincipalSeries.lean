import Langlands.Representation.Unramified.Eigenvalues
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Representation.Category.ClassInvariants

/-! # Spectra and actual unramified principal-series constituents -/

noncomputable section

namespace Langlands.Unramified

open Correspondence

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance spectrumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance spectrumGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance spectrumGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The continuous unramified character whose uniformizer value is `z`. -/
def character (z : ℂˣ) : QuasiCharacter F :=
  F.canonicalTopologicalData.unramifiedCharacterContinuous z

@[simp] theorem character_apply (z : ℂˣ) (a : F.Carrierˣ) :
    character F z a = z ^ F.canonicalTopologicalData.ord (a : F.Carrier) := rfl

@[simp] theorem character_uniformizer (z : ℂˣ) :
    character F z F.canonicalTopologicalData.uniformizerUnit = z :=
  F.canonicalTopologicalData.unramifiedCharacter_uniformizer z

theorem character_isUnramified (z : ℂˣ) :
    F.canonicalTopologicalData.IsUnramifiedCharacter (character F z).toMonoidHom :=
  F.canonicalTopologicalData.isUnramifiedCharacter z

/-- Evaluation recovers every unramified continuous character. -/
theorem character_eq_of_unramified (χ : QuasiCharacter F)
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom) :
    character F (χ F.canonicalTopologicalData.uniformizerUnit) = χ := by
  apply ContinuousMonoidHom.ext
  intro a
  exact congrArg (fun η : F.Carrierˣ →* ℂˣ => η a)
    (F.canonicalTopologicalData.eq_unramifiedCharacter χ.toMonoidHom hχ).symm

/-- Ordered unramified inducing characters from an ordered unit spectrum. -/
def characterTuple {n : ℕ} (z : Fin n → ℂˣ) : Fin n → QuasiCharacter F :=
  fun i => character F (z i)

/-- Uniformizer values of a tuple of continuous characters. -/
def characterValues {n : ℕ} (χ : Fin n → QuasiCharacter F) : Fin n → ℂˣ :=
  fun i => χ i F.canonicalTopologicalData.uniformizerUnit

/-- The unordered uniformizer spectrum, retaining all multiplicities. -/
def characterSpectrum {n : ℕ} (χ : Fin n → QuasiCharacter F) : Eigenvalues n :=
  Eigenvalues.ofTuple (characterValues F χ)

@[simp] theorem characterValues_characterTuple {n : ℕ} (z : Fin n → ℂˣ) :
    characterValues F (characterTuple F z) = z := by
  funext i
  exact character_uniformizer F (z i)

@[simp] theorem characterSpectrum_characterTuple {n : ℕ} (z : Fin n → ℂˣ) :
    characterSpectrum F (characterTuple F z) = Eigenvalues.ofTuple z := by
  rw [characterSpectrum, characterValues_characterTuple]

theorem characterTuple_characterValues {n : ℕ} (χ : Fin n → QuasiCharacter F)
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) :
    characterTuple F (characterValues F χ) = χ := by
  funext i
  exact character_eq_of_unramified F (χ i) (hχ i)

theorem characterTuple_isUnramified {n : ℕ} (z : Fin n → ℂˣ) (i : Fin n) :
    F.canonicalTopologicalData.IsUnramifiedCharacter (characterTuple F z i).toMonoidHom :=
  character_isUnramified F (z i)

/-- Every spectrum is realized by actual continuous unramified field characters. -/
theorem exists_characterTuple {n : ℕ} (s : Eigenvalues n) :
    ∃ χ : Fin n → QuasiCharacter F,
      (∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) ∧
      characterSpectrum F χ = s := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n s
  exact ⟨characterTuple F z, characterTuple_isUnramified F z,
    characterSpectrum_characterTuple F z⟩

/-- The existing normalized upper-Borel induction, with inducing character
values specified at the canonical uniformizer. -/
def principalSeriesOfTuple {r : ℕ} (z : Fin (r + 1) → ℂˣ) :=
  principalSeries F r (characterTuple F z)

section SubquotientTransport

variable {G : Type*} [Group G]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G U} {π : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The actual subquotient relation is invariant under an equivalence of its target. -/
theorem isSubquotientOf_iff_of_equiv (e : π.Equiv σ) :
    IsSubquotientOf ρ π ↔ IsSubquotientOf ρ σ := by
  constructor
  · rintro ⟨S, f, hf⟩
    exact ⟨S, e.toIntertwiningMap.comp f, e.surjective.comp hf⟩
  · rintro ⟨S, f, hf⟩
    exact ⟨S, e.symm.toIntertwiningMap.comp f, e.symm.surjective.comp hf⟩

end SubquotientTransport

/-- An actual irreducible admissible smooth object is a spherical subquotient of
this ordered normalized principal series. No genericity condition is imposed. -/
def IsSphericalConstituent {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat) : Prop :=
  fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ ∧
    IsSubquotientOf (principalSeriesOfTuple F z) A.obj.representation

/-- An unordered spectrum is related to an actual object when some enumeration
induces a principal series having that object as a spherical subquotient. -/
def HasSphericalSpectrum {r : ℕ} (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (s : Eigenvalues (r + 1)) : Prop :=
  ∃ z : Fin (r + 1) → ℂˣ, Eigenvalues.ofTuple z = s ∧ IsSphericalConstituent F z A

theorem isSphericalConstituent_iff_of_equiv {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    {A : AutomorphicObject.{uF, uV} F r.succPNat}
    {B : AutomorphicObject.{uF, uW} F r.succPNat}
    (e : A.obj.representation.Equiv B.obj.representation) :
    IsSphericalConstituent F z A ↔ IsSphericalConstituent F z B :=
  and_congr (fixedVectors_ne_bot_iff_of_equiv e (sphericalSubgroup F r))
    (isSubquotientOf_iff_of_equiv e)

theorem hasSphericalSpectrum_iff_of_equiv {r : ℕ}
    {A : AutomorphicObject.{uF, uV} F r.succPNat}
    {B : AutomorphicObject.{uF, uW} F r.succPNat}
    (e : A.obj.representation.Equiv B.obj.representation) (s : Eigenvalues (r + 1)) :
    HasSphericalSpectrum F A s ↔ HasSphericalSpectrum F B s := by
  unfold HasSphericalSpectrum
  exact exists_congr fun z => and_congr Iff.rfl
    (isSphericalConstituent_iff_of_equiv F z e)

/-- The same relation on the genuine quotient by representation isomorphism. -/
def HasSphericalSpectrumClass {r : ℕ} (π : AutomorphicClass.{uF, uV} F r.succPNat)
    (s : Eigenvalues (r + 1)) : Prop :=
  ∃ A : AutomorphicObject.{uF, uV} F r.succPNat,
    automorphicClassOf F A = π ∧ HasSphericalSpectrum F A s

@[simp] theorem hasSphericalSpectrumClass_classOf {r : ℕ}
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (s : Eigenvalues (r + 1)) :
    HasSphericalSpectrumClass F (automorphicClassOf F A) s ↔ HasSphericalSpectrum F A s := by
  constructor
  · rintro ⟨B, hB, h⟩
    obtain ⟨e⟩ := (automorphicClassOf_eq_iff F B A).mp hB
    exact (hasSphericalSpectrum_iff_of_equiv F e s).mp h
  · intro h
    exact ⟨A, rfl, h⟩

theorem HasSphericalSpectrumClass.isSpherical {r : ℕ}
    {π : AutomorphicClass.{uF, uV} F r.succPNat} {s : Eigenvalues (r + 1)}
    (h : HasSphericalSpectrumClass F π s) : IsSphericalClass F π := by
  obtain ⟨A, hA, z, _, hz⟩ := h
  exact ⟨A, hA, hz.1⟩

/-- The relation can equivalently be expressed using any actual unramified
inducing characters and their uniformizer values. -/
theorem hasSphericalSpectrum_iff_characters {r : ℕ}
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (s : Eigenvalues (r + 1)) :
    HasSphericalSpectrum F A s ↔
      ∃ χ : Fin (r + 1) → QuasiCharacter F,
        (∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom) ∧
        characterSpectrum F χ = s ∧
        fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ ∧
        IsSubquotientOf (principalSeries F r χ) A.obj.representation := by
  constructor
  · rintro ⟨z, hz, hA⟩
    exact ⟨characterTuple F z, characterTuple_isUnramified F z,
      (characterSpectrum_characterTuple F z).trans hz, hA⟩
  · rintro ⟨χ, hχ, hs, hfixed, hsub⟩
    refine ⟨characterValues F χ, hs, hfixed, ?_⟩
    unfold principalSeriesOfTuple
    rw [characterTuple_characterValues F χ hχ]
    exact hsub

end Langlands.Unramified
