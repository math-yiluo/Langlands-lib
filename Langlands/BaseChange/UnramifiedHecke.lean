import Langlands.Representation.Unramified.SphericalHeckeGenerationProof
import Langlands.Representation.Unramified.SphericalHeckeDetermination

/-!
# Satake characters and the unramified base-change homomorphism

Henniart–Lemaire (2011), Chapter I, §I.1.3 (printed p. 6) and §I.3.1 (printed
pp. 24–25). The Library has no Satake transform; the characters `φ ↦ S_F(φ)(s)` of
the spherical Hecke algebra are characterized by their values on the standard
double-coset elements (`IsSatakeCharacter`), and the base-change homomorphism
`b : H_E → H_F` by the identity `S_F(b φ)(s) = S_E(φ)(s^l)` on these characters
(`IsUnramifiedBaseChangeHom`). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified

universe u v uV uW

local instance unramifiedHeckeFieldTopology {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance unramifiedHeckeFieldValuativeRel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance unramifiedHeckeFieldLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance unramifiedHeckeGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance unramifiedHeckeGeneralLinearTopologicalGroup {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n
local instance unramifiedHeckeGeneralLinearT2 {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance unramifiedHeckeGeneralLinearMeasurable {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) :=
  borel _
local instance unramifiedHeckeGeneralLinearBorel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) :=
  ⟨rfl⟩

variable {p : ℕ} [Fact p.Prime]

/-- `ω` is the Satake character at the parameter `s`: the algebra character
`φ ↦ S_F(φ)(s)` of the spherical Hecke algebra of `GL_{r+1}(F)`, characterized by its
values `q^{i(r+1-i)/2} e_i(s)` on the characteristic functions of the standard double
cosets `K ϖ^{(i)} K` (HL I.3.1, printed pp. 24–25). -/
def IsSatakeCharacter (F : PadicField.{u} p) (r : ℕ) (s : Eigenvalues (r + 1))
    (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ) : Prop :=
  ∀ i : Fin (r + 2), ω (standardHeckeElement F r i) = standardHeckeScalar F s i

/-- `b : H_E → H_F` is the unramified base-change homomorphism of degree `l`, defined by
`S_F(b φ)(X_1, …, X_n) = S_E(φ)(X_1^l, …, X_n^l)` (HL I.1.3, printed p. 6; I.3.1,
printed p. 25): composing `b` with the Satake character of `F` at `s` gives the Satake
character of `E` at `s^l`. -/
def IsUnramifiedBaseChangeHom (F : PadicField.{u} p) (E : PadicField.{v} p) (l r : ℕ)
    (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r) : Prop :=
  ∀ (s : Eigenvalues (r + 1)) (ωF : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ)
    (ωE : SphericalHeckeAlgebra E r →ₐ[ℂ] ℂ),
    IsSatakeCharacter F r s ωF → IsSatakeCharacter E r (Eigenvalues.power s l) ωE →
      ωF.comp b = ωE

/-- A Satake character is determined by its parameter. -/
theorem IsSatakeCharacter.unique {F : PadicField.{u} p} {r : ℕ} {s : Eigenvalues (r + 1)}
    {ω ω' : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ} (h : IsSatakeCharacter F r s ω)
    (h' : IsSatakeCharacter F r s ω') : ω = ω' := by
  have hadj : Set.EqOn ω ω' (Algebra.adjoin ℂ (Set.range (standardHeckeElement F r))) := by
    rw [AlgHom.eqOn_adjoin_iff]
    rintro _ ⟨i, rfl⟩
    rw [h i, h' i]
  ext f
  obtain ⟨m, hm⟩ := sphericalHeckeGeneration p F r f
  have hT := hadj hm
  simp only [map_mul, map_pow] at hT
  rw [h (Fin.last (r + 1)), h' (Fin.last (r + 1))] at hT
  exact mul_left_cancel₀ (pow_ne_zero _ (standardHeckeScalar_last_ne_zero F s)) hT

/-- On a nonzero module, scalar endomorphisms determine their scalar. -/
theorem algebraMap_end_injective_of_ne_bot {M : Type*} [AddCommGroup M] [Module ℂ M]
    {N : Submodule ℂ M} (hN : N ≠ ⊥) : Function.Injective (algebraMap ℂ (Module.End ℂ N)) := by
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  exact (algebraMap ℂ (Module.End ℂ N)).injective

/-- On an irreducible admissible representation with spherical Hecke spectrum `s`, the
spherical Hecke algebra acts on the `K`-fixed vectors through the Satake character at
`s`. -/
theorem exists_isSatakeCharacter_of_hasSphericalHeckeSpectrum {F : PadicField.{u} p} {r : ℕ}
    {A : AutomorphicObject.{u, uV} F r.succPNat} {s : Eigenvalues (r + 1)}
    (hA : HasSphericalHeckeSpectrum F A s) :
    ∃ ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ, IsSatakeCharacter F r s ω ∧
      ∀ f : SphericalHeckeAlgebra F r, sphericalCornerAction F A f = algebraMap ℂ _ (ω f) := by
  have hinj := algebraMap_end_injective_of_ne_bot hA.1
  have hmem : ∀ f : SphericalHeckeAlgebra F r,
      sphericalCornerAction F A f ∈ (⊥ : Subalgebra ℂ (Module.End ℂ
        (fixedVectors A.obj.representation (sphericalSubgroup F r)))) := by
    intro f
    obtain ⟨c, hc, -⟩ := exists_common_scalar F sphericalHeckeGeneration hA hA f
    rw [hc]
    exact Algebra.mem_bot.mpr ⟨c, rfl⟩
  let e := Algebra.botEquivOfInjective hinj
  let ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ :=
    e.toAlgHom.comp ((sphericalCornerAction F A).codRestrict ⊥ hmem)
  have hω : ∀ f : SphericalHeckeAlgebra F r,
      sphericalCornerAction F A f = algebraMap ℂ _ (ω f) := by
    intro f
    have h := congrArg Subtype.val
      (e.symm_apply_apply ((sphericalCornerAction F A).codRestrict ⊥ hmem f))
    exact h.symm
  refine ⟨ω, fun i => hinj ?_, hω⟩
  rw [← hω, sphericalCornerAction_standardHeckeElement_of_hasSpectrum F hA]

/-- The base-change homomorphism is dual to unramified base change of spherical
representations: if `A` has spherical spectrum `s` and `B` has spectrum `s^l`, every
`φ` acting on the spherical vectors of `B` by `c` has `b φ` acting on those of `A` by `c`
(HL I.1.3). -/
theorem IsUnramifiedBaseChangeHom.sphericalCornerAction_eq {F : PadicField.{u} p}
    {E : PadicField.{v} p} {l r : ℕ}
    {b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r}
    (hb : IsUnramifiedBaseChangeHom F E l r b)
    {A : AutomorphicObject.{u, uV} F r.succPNat} {B : AutomorphicObject.{v, uW} E r.succPNat}
    {s : Eigenvalues (r + 1)} (hA : HasSphericalHeckeSpectrum F A s)
    (hB : HasSphericalHeckeSpectrum E B (Eigenvalues.power s l))
    (φ : SphericalHeckeAlgebra E r) (c : ℂ)
    (hc : sphericalCornerAction E B φ = algebraMap ℂ _ c) :
    sphericalCornerAction F A (b φ) = algebraMap ℂ _ c := by
  obtain ⟨ωF, hωF, hAω⟩ := exists_isSatakeCharacter_of_hasSphericalHeckeSpectrum hA
  obtain ⟨ωE, hωE, hBω⟩ := exists_isSatakeCharacter_of_hasSphericalHeckeSpectrum hB
  have hφ : ωE φ = c := algebraMap_end_injective_of_ne_bot hB.1 ((hBω φ).symm.trans hc)
  rw [hAω, ← AlgHom.comp_apply, hb s ωF ωE hωF hωE, hφ]

end Langlands.BaseChange
