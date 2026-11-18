import Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises
import Langlands.Representation.Archimedean.ComplexTransposeStandardDuality
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueProof
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction

/-! # The local pairing premise at a complex place

This module proves `ComplexStandardPairingParameterStatement`: if the `U(n)`-finite complex
standard modules of two lists `d`, `dd` of `n` complex characters are irreducible
`(𝔤, K)`-modules and carry a nonzero invariant bilinear pairing, then `dd` is a permutation of
the list of inverse characters of `d`.

The pairing turns the standard module of `dd` into a nonzero intertwining map into the
`U(n)`-finite dual of the standard module of `d`. That dual is irreducible and admissible, and
by the Library's inverse-character duality it is the standard module of the inverse characters
of `d`. After sorting both lists into the Langlands order, the uniqueness half of the Langlands
classification identifies the two lists up to permutation. See the paired Markdown.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean
  Langlands.KFiniteDual

namespace ComplexStandardPairing

/-! ### The two inverse characters agree -/

/-- Two character data with the same character, weight and exponent are equal. -/
theorem complexCharacterData_ext {d e : ComplexCharacterData} (hc : d.character = e.character)
    (hw : d.weight = e.weight) (he : d.exponent = e.exponent) : d = e := by
  cases d
  cases e
  cases hc
  cases hw
  cases he
  rfl

/-- `ComplexCharacterData.inv` and `complexCharacterDataInv` are the same inverse character. -/
theorem inv_eq_complexCharacterDataInv (d : ComplexCharacterData) :
    d.inv = complexCharacterDataInv d :=
  complexCharacterData_ext (by ext z; rfl) rfl rfl

/-! ### Translations and derivatives as the standard `(𝔤, K)`-module actions -/

variable {n : ℕ} {ds : List ComplexCharacterData}

theorem translate_eq_rep (k : unitaryCompact ℂ n) (f : complexStandardKFinite n ds) :
    complexStandardTranslate n ds k f = complexStandardRep n ds ⟨_, k.2⟩ f := by
  obtain ⟨_, e⟩ := (isComplexStandardIntertwining_id n ds).1 k f
  exact e

theorem rep_eq_translate (k : Matrix.unitaryGroup (Fin n) ℂ) (f : complexStandardKFinite n ds) :
    complexStandardRep n ds k f = complexStandardTranslate n ds ⟨Unitary.toUnits k, k.2⟩ f :=
  (translate_eq_rep ⟨Unitary.toUnits k, k.2⟩ f).symm

theorem derivative_eq_lie (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds) :
    complexStandardDerivative n ds X f = complexStandardLie n ds (1 ⊗ₜ X) f := by
  obtain ⟨_, e⟩ := (isComplexStandardIntertwining_id n ds).2 X f
  exact e

/-- `IsComplexStandardIrreducible` is irreducibility of the standard `(𝔤, K)`-module. -/
theorem isIrreducibleGKModule_of_isComplexStandardIrreducible
    (h : IsComplexStandardIrreducible n ds) :
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) := by
  refine ⟨h.1, fun W hWk hWX => h.2 W (fun k f hf => ?_) (fun X f hf => ?_)⟩
  · rw [translate_eq_rep]
    exact hWk _ f hf
  · rw [derivative_eq_lie]
    exact hWX _ f hf

/-! ### The pairing as a map into the finite dual -/

section Pairing

variable {d dd : List ComplexCharacterData}
  {P : complexStandardKFinite n d →ₗ[ℂ] complexStandardKFinite n dd →ₗ[ℂ] ℂ}

theorem pairing_rep (hP : IsComplexStandardInvariantPairing n d dd P)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : complexStandardKFinite n d)
    (f' : complexStandardKFinite n dd) :
    P (complexStandardRep n d k f) (complexStandardRep n dd k f') = P f f' := by
  rw [rep_eq_translate, rep_eq_translate]
  exact hP.1 _ f f'

theorem pairing_lie (hP : IsComplexStandardInvariantPairing n d dd P)
    (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n d)
    (f' : complexStandardKFinite n dd) :
    P (complexStandardLie n d (1 ⊗ₜ X) f) f' + P f (complexStandardLie n dd (1 ⊗ₜ X) f') = 0 := by
  rw [← derivative_eq_lie, ← derivative_eq_lie]
  exact hP.2 X f f'

theorem flip_rep (hP : IsComplexStandardInvariantPairing n d dd P)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f' : complexStandardKFinite n dd) :
    P.flip (complexStandardRep n dd k f') = (complexStandardRep n d).dual k (P.flip f') := by
  refine LinearMap.ext fun f => ?_
  rw [dual_apply_apply, LinearMap.flip_apply, LinearMap.flip_apply]
  have h := pairing_rep hP k (complexStandardRep n d k⁻¹ f) f'
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

theorem flip_lie (hP : IsComplexStandardInvariantPairing n d dd P)
    (X : Matrix (Fin n) (Fin n) ℂ) (f' : complexStandardKFinite n dd)
    (f : complexStandardKFinite n d) :
    P.flip (complexStandardLie n dd (1 ⊗ₜ X) f') f =
      -(P.flip f' (complexStandardLie n d (1 ⊗ₜ X) f)) := by
  rw [LinearMap.flip_apply, LinearMap.flip_apply]
  linear_combination pairing_lie hP X f f'

end Pairing

end ComplexStandardPairing

open ComplexStandardPairing

/-- **The local pairing premise.** -/
theorem complexStandardPairingParameter : ComplexStandardPairingParameterStatement := by
  intro n d dd hd hdd hirr hirr' P hP hP0
  have hgk := isComplexGKModule_complexStandardModule n d
  have hirrd := isIrreducibleGKModule_of_isComplexStandardIrreducible hirr
  have hirrdd := isIrreducibleGKModule_of_isComplexStandardIrreducible hirr'
  have hadm : IsAdmissibleGKModule (complexStandardRep n d) :=
    ComplexStandardHomTransposeProof.isAdmissibleGKModule_principalSeriesRep (n := n)
      (complexPositionCharacter d)
  -- The finite dual of the standard module of `d`.
  have hgkV := ComplexContragredient.isComplexGKModule_kDual hgk
  have hirrV := ComplexContragredient.isIrreducible_kDual hgk hirrd hadm
  have hadmV : IsAdmissibleGKModule (kDualRep (complexStandardRep n d)) :=
    admissible_kDual hgk.1 hgk.2.1 hadm
  -- The pairing as an intertwining map from the standard module of `dd` into the finite dual.
  let φ : complexStandardKFinite n dd →ₗ[ℂ] kDual (complexStandardRep n d) :=
    P.flip.codRestrict _ fun f' =>
      ComplexStandardHomTransposeProof.isFiniteVector_dual_of_equivariant P.flip (flip_rep hP)
        ((isComplexGKModule_complexStandardModule n dd).1 f')
  have hφρ : ∀ k v, φ (complexStandardRep n dd k v) =
      kDualRep (complexStandardRep n d) k (φ v) :=
    fun k v => Subtype.ext (flip_rep hP k v)
  have hφπ : ∀ X v, φ (complexStandardLie n dd (1 ⊗ₜ X) v) =
      ComplexContragredient.dualLie hgk (1 ⊗ₜ X) (φ v) :=
    fun X v => Subtype.ext (LinearMap.ext fun f => flip_lie hP X v f)
  have hφ0 : φ ≠ 0 := by
    intro h
    apply hP0
    refine LinearMap.ext fun f => LinearMap.ext fun f' => ?_
    exact congrArg (fun w : kDual (complexStandardRep n d) =>
      (w : Module.Dual ℂ (complexStandardKFinite n d)) f) (LinearMap.congr_fun h f')
  -- The inverse-character standard module is the finite dual, hence irreducible.
  let ψ := ComplexTransposeStandardDuality.dualEquiv n d
  have hψ : IsComplexStandardIntertwining n (kDualRep (complexStandardRep n d))
      (ComplexContragredient.dualLie hgk) (d.map complexCharacterDataInv) ψ.toLinearMap := by
    have h := (isComplexStandardIntertwining_id n (d.map complexCharacterDataInv)).comp
      ψ.toLinearMap (fun k v => ComplexTransposeStandardDuality.dualEquiv_rep d k v)
      (fun X v => ComplexTransposeStandardDuality.dualEquiv_lie d (1 ⊗ₜ X) v)
    rwa [LinearMap.comp_id] at h
  have hlenInv : (d.map complexCharacterDataInv).length = n := by
    rw [List.length_map, hd]
  have hirrInv := isIrreducibleGKModule_of_injective hirrV hψ ψ.injective
    (complexStandardNontrivial n _ hlenInv)
  -- Sort both lists into the Langlands order.
  have hperm₁ : (dd.mergeSort complexLanglandsLE).Perm dd :=
    List.mergeSort_perm dd complexLanglandsLE
  have hperm₂ : ((d.map complexCharacterDataInv).mergeSort complexLanglandsLE).Perm
      (d.map complexCharacterDataInv) :=
    List.mergeSort_perm _ complexLanglandsLE
  obtain ⟨T₁, hT₁bij, hT₁⟩ := complexStandardPermutation n dd _ hdd hperm₁ hirrdd
  obtain ⟨T₂, hT₂bij, hT₂⟩ := complexStandardPermutation n _ _ hlenInv hperm₂ hirrInv
  have hA := hT₁.comp φ hφρ hφπ
  have hB := hT₂.comp ψ.toLinearMap (fun k v => hψ.map_rep k v)
    (fun X v => hψ.map_lie (1 ⊗ₜ X) v)
  have hA0 : φ ∘ₗ T₁ ≠ 0 := by
    intro h
    apply hφ0
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := hT₁bij.2 v
    exact LinearMap.congr_fun h f
  have hlen₂ := hperm₂.length_eq.trans hlenInv
  have hB0 : ψ.toLinearMap ∘ₗ T₂ ≠ 0 := by
    have := complexStandardNontrivial n _ hlen₂
    obtain ⟨f, hf⟩ := exists_ne (0 : kFiniteFunctions
      (complexStandardModule n ((d.map complexCharacterDataInv).mergeSort complexLanglandsLE))
      (unitaryCompact ℂ n))
    intro h
    apply hf
    apply ψ.injective.comp hT₂bij.1
    simpa using LinearMap.congr_fun h f
  have h₁₂ := complexLanglandsQuotientUnique n _ _ _ _ _ _ _ hgkV hirrV hadmV
    (hperm₁.length_eq.trans hdd) hlen₂ (isComplexLanglandsOrdered_mergeSort dd)
    (isComplexLanglandsOrdered_mergeSort _) hA0 hA hB0 hB
  have hmap : d.map ComplexCharacterData.inv = d.map complexCharacterDataInv :=
    List.map_congr_left fun x _ => inv_eq_complexCharacterDataInv x
  rw [hmap]
  exact hperm₁.symm.trans (h₁₂.trans hperm₂)

end Langlands.Global.RankinSelbergGlobal
