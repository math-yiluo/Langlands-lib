/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!
# The `ℓ`-adic coefficient rings of an abstract finite extension

A finite extension `E` of `ℚ_ℓ` embeds into `ℚ̄_ℓ`, and its image `E'` is a finite subextension
of `ℚ̄_ℓ`. This file shows that the condensed coefficient rings attached to `E` are isomorphic,
as ring objects, to those attached to `E'`, so that statements about the coefficient rings of
finite subextensions of `ℚ̄_ℓ` (indexed by `PadicAlgCl.FiniteIntermediateField ℓ`) apply to
abstract finite extensions.

## Main results

* `Profinite.continuousMapRingObjIso`: a ring isomorphism which is a homeomorphism induces an
  isomorphism of condensed rings `T̲ ≅ T̲'`.
* `Profinite.exists_continuousMapRingObj_iso`: for a finite extension `E` of `ℚ_ℓ` (as a normed
  field), `E̲` is isomorphic to `E̲'` for a finite subextension `E'` of `ℚ̄_ℓ`.
* `Profinite.exists_padicIntegersRingObj_iso`: for a subfield `E ⊆ ℚ̄_ℓ` given by an embedding,
  finite over `ℚ_ℓ`, `𝒪̲_E` is isomorphic to `𝒪̲_{E'}` for the image `E'` of `E`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace Profinite

section Iso

variable {T T' : Type} [TopologicalSpace T] [TopologicalSpace T'] [Ring T] [IsTopologicalRing T]
  [Ring T'] [IsTopologicalRing T']

/-- A ring isomorphism `φ : T ≃+* T'` which is continuous in both directions induces, by
postcomposition, an isomorphism of condensed rings `C(-, T) ≅ C(-, T')`. -/
noncomputable def continuousMapRingObjIso (φ : T ≃+* T') (hφ : Continuous φ)
    (hφ' : Continuous φ.symm) : continuousMapRingObj.{u} T ≅ continuousMapRingObj.{u} T' where
  hom := continuousMapRingObjMap φ.toRingHom hφ
  inv := continuousMapRingObjMap φ.symm.toRingHom hφ'
  hom_inv_id := by
    rw [← continuousMapRingObjMap_comp]
    exact continuousMapRingObjMap_eq_id _ _ (RingEquiv.symm_toRingHom_comp_toRingHom φ)
  inv_hom_id := by
    rw [← continuousMapRingObjMap_comp]
    exact continuousMapRingObjMap_eq_id _ _ (RingEquiv.toRingHom_comp_symm_toRingHom φ)

/-- The isomorphism `continuousMapRingObjIso` is an isomorphism of ring objects. -/
instance isMonHom_continuousMapRingObjIso_hom (φ : T ≃+* T') (hφ : Continuous φ)
    (hφ' : Continuous φ.symm) : IsMonHom (continuousMapRingObjIso.{u} φ hφ hφ').hom :=
  inferInstanceAs (IsMonHom (continuousMapRingObjMap φ.toRingHom hφ))

end Iso

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A finite extension `E` of `ℚ_ℓ` (as a normed field) has condensed ring `E̲` isomorphic to that
of a finite subextension of `ℚ̄_ℓ`. -/
theorem exists_continuousMapRingObj_iso (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (E' : PadicAlgCl.FiniteIntermediateField ℓ)
      (e : continuousMapRingObj.{u} E ≅ continuousMapRingObj.{u} E'.1), IsMonHom e.hom := by
  let σ : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let φ : E ≃ₐ[ℚ_[ℓ]] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  have hfin : FiniteDimensional ℚ_[ℓ] σ.fieldRange := φ.toLinearEquiv.finiteDimensional
  have hφ : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hφ' : Continuous φ.symm := φ.symm.toLinearMap.continuous_of_finiteDimensional
  exact ⟨⟨σ.fieldRange, hfin⟩, continuousMapRingObjIso φ.toRingEquiv hφ hφ', inferInstance⟩

/-- For a subfield `E ⊆ ℚ̄_ℓ` given by an embedding, finite over `ℚ_ℓ`, `𝒪̲_E` is isomorphic to
`𝒪̲_{E'}` for the image `E'` of `E`. -/
theorem exists_padicIntegersRingObj_iso (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (E' : PadicAlgCl.FiniteIntermediateField ℓ)
      (e : padicIntegersRingObj.{u} ℓ E ≅ padicIntegersRingObj.{u} ℓ E'.1), IsMonHom e.hom := by
  let σ : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let φ : E ≃ₐ[ℚ_[ℓ]] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  have hfin : FiniteDimensional ℚ_[ℓ] σ.fieldRange := φ.toLinearEquiv.finiteDimensional
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ σ.fieldRange
  have h : (PadicAlgCl.integers ℓ E).toSubring.map φ.toRingEquiv.toRingHom =
      (PadicAlgCl.integers ℓ σ.fieldRange).toSubring := by
    ext y
    refine ⟨?_, fun hy ↦ ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · rw [← φ.apply_symm_apply y] at hy
      exact hy
  let ψ : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ σ.fieldRange :=
    RingEquiv.trans (φ.toRingEquiv.subringMap (s := (PadicAlgCl.integers ℓ E).toSubring))
      (RingEquiv.subringCongr h)
  have hψ : Continuous ψ := continuous_induced_rng.2 (continuous_induced_rng.2
    (continuous_induced_dom.comp continuous_subtype_val :
      Continuous fun x : PadicAlgCl.integers ℓ E ↦ algebraMap E (PadicAlgCl ℓ) x))
  have hψ' : Continuous ψ.symm := continuous_induced_rng.2 (continuous_induced_rng.2
    ((continuous_induced_dom.comp continuous_subtype_val :
      Continuous fun y : PadicAlgCl.integers ℓ σ.fieldRange ↦
        algebraMap σ.fieldRange (PadicAlgCl ℓ) y).congr fun y ↦
      (congrArg (fun z : PadicAlgCl.integers ℓ σ.fieldRange ↦
        algebraMap σ.fieldRange (PadicAlgCl ℓ) z) (ψ.apply_symm_apply y)).symm))
  exact ⟨⟨σ.fieldRange, hfin⟩, continuousMapRingObjIso ψ hψ hψ', inferInstance⟩

end EllAdic

end Profinite
