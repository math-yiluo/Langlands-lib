/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.RingTheory.AlgebraicIndependent.Basic
@[expose] public section
set_option autoImplicit false
universe u
namespace AlgebraicGeometry
/-- Separably generated extensions transport across a residue-field ring equivalence.
Source: Stacks Project, Tag 030O (definition of separable generation).
Proof: keep the same subset of E as transcendence basis. Transport algebraic
independence in both directions along e, using the compatibility of algebra maps;
maximality is therefore unchanged. Surjectivity of e and compatibility show that
the coefficient fields have the same image in E. Their intermediate fields
adjoining the basis thus have equal underlying subfields. The identity of these
subfields is a ring equivalence commuting with their embeddings in E. Transport
separability along this equivalence and the identity equivalence of E.
(blueprint: lem-sbc-reduced-generic-fibre-field-embedding-transport) -/
theorem separablyGenerated_of_residueField_equiv
    (K K' E : Type u) [Field K] [Field K'] [Field E]
    (e : K ≃+* K') [Algebra K E] [Algebra K' E]
    (hcompat : ∀ x : K, algebraMap K E x = algebraMap K' E (e x))
    (h : Algebra.IsSeparablyGenerated K' E) :
    Algebra.IsSeparablyGenerated K E := by
  obtain ⟨s, hs, hsep⟩ := h
  have hc : (algebraMap K' E).comp e.toRingHom =
      (RingHom.id E).comp (algebraMap K E) := by
    ext x
    exact (hcompat x).symm
  have hi (t : Set E) :
      AlgebraicIndependent K' ((↑) : t → E) ↔
        AlgebraicIndependent K ((↑) : t → E) :=
    algebraicIndependent_ringHom_iff_of_comp_eq e (RingHom.id E)
      Function.injective_id hc
  have hb : IsTranscendenceBasis K ((↑) : s → E) := by
    refine ⟨(hi s).mp hs.1, ?_⟩
    intro t ht hst
    exact hs.2 t ((hi t).mpr ht) hst
  have hr : Set.range (algebraMap K E) = Set.range (algebraMap K' E) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, (hcompat a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e.symm a, by simpa using hcompat (e.symm a)⟩
  have hf : (IntermediateField.adjoin K' s).toSubfield =
      (IntermediateField.adjoin K s).toSubfield := by
    simp only [IntermediateField.adjoin_toSubfield, hr]
  let ef : IntermediateField.adjoin K' s ≃+* IntermediateField.adjoin K s :=
    RingEquiv.subfieldCongr hf
  let := hsep
  refine ⟨s, hb, Algebra.IsSeparable.of_equiv_equiv ef (RingEquiv.refl E) ?_⟩
  ext x
  rfl
end AlgebraicGeometry
