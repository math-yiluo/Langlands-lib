/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Classification

/-!
# Extending isomorphisms of uncountable algebraically closed fields

Mathlib's `IsAlgClosed.equivOfTranscendenceBasis` builds a ring isomorphism between two
algebraically closed `R`-algebras with equipotent transcendence bases. We record that the
construction is `R`-linear (`IsAlgClosed.algEquivOfTranscendenceBasis`), and deduce that an
embedding `σ : F →+* L` of a countable field `F ⊆ K` extends to an isomorphism `K ≃+* L` when
`K` and `L` are algebraically closed, uncountable and of the same cardinality.

## Main statements

- `IsAlgClosed.algEquivOfTranscendenceBasis`: the `R`-algebra version of
  `IsAlgClosed.equivOfTranscendenceBasis`.
- `IsAlgClosed.exists_ringEquiv_extend`: extension of embeddings of countable subfields to
  isomorphisms of uncountable algebraically closed fields of the same cardinality.
-/

@[expose] public section

universe u v

open Cardinal

namespace IsAlgClosed

section Classification

variable {R L K : Type*} [CommRing R]
variable [Field K] [Algebra R K]
variable [Field L] [Algebra R L]
variable {ι : Type*} (v : ι → K)
variable {κ : Type*} (w : κ → L)

/-- Two algebraically closed `R`-algebras with equipotent transcendence bases over `R` are
isomorphic as `R`-algebras. This is the `R`-linear version of
`IsAlgClosed.equivOfTranscendenceBasis`. -/
noncomputable def algEquivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
    (hv : IsTranscendenceBasis R v) (hw : IsTranscendenceBasis R w) : K ≃ₐ[R] L :=
  letI := isAlgClosure_of_transcendence_basis v hv
  letI := isAlgClosure_of_transcendence_basis w hw
  let eS : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  AlgEquiv.ofRingEquiv (f := IsAlgClosure.equivOfEquiv K L eS.toRingEquiv) fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
      IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]

end Classification

variable {K : Type u} {L : Type v} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]

/-- Let `K` and `L` be uncountable algebraically closed fields of the same cardinality, and let
`F` be a countable field with `K` an `F`-algebra. Then every field embedding `σ : F →+* L`
extends to a ring isomorphism `K ≃+* L`: transcendence bases of `K` over `F` and of `L` over `F`
(via `σ`) both have cardinality `#K = #L`. -/
theorem exists_ringEquiv_extend {F : Type*} [Field F] [Algebra F K] (hF : #F ≤ ℵ₀)
    (hK : ℵ₀ < #K) (hKL : Nonempty (K ≃ L)) (σ : F →+* L) :
    ∃ e : K ≃+* L, ∀ x : F, e (algebraMap F K x) = σ x := by
  let : Algebra F L := σ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hF hK),
      ← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hF hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  refine ⟨(algEquivOfTranscendenceBasis _ _ e hs ht).toRingEquiv, fun x ↦ ?_⟩
  exact (algEquivOfTranscendenceBasis _ _ e hs ht).commutes x

end IsAlgClosed
