import Langlands.AlgebraicGeometry.GroupoidCoactionInvariants
import Langlands.AlgebraicGeometry.FiniteLocallyFreeInvariantRingQuotientProof
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Tensor presentations for finite projective equivalence relations -/

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelation

open GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

lemma range_sup_eq_top (hE : RingEtaleEquivalenceRelation t) :
    (algebraMap B C).range ⊔ t.range = ⊤ := by
  have h := congrArg Subalgebra.toSubring hE.adjoin_range_eq_top
  simpa only [Algebra.adjoin_eq_ring_closure, Subring.closure_union,
    ← RingHom.coe_range, Subring.closure_eq, Algebra.top_toSubring] using h

lemma source_target_equivalence (hE : RingEtaleEquivalenceRelation t)
    (T : Type u) [CommRing T] :
    _root_.Equivalence fun x y : B →+* T =>
      ∃ φ : C →+* T, φ.comp (algebraMap B C) = x ∧ φ.comp t = y := by
  constructor
  · intro x
    obtain ⟨φ, ht, hs⟩ := hE.refl T x
    exact ⟨φ, hs, ht⟩
  · rintro x y ⟨φ, hs, ht⟩
    obtain ⟨ψ, hψt, hψs⟩ := hE.symm T φ
    exact ⟨ψ, hψs.trans ht, hψt.trans hs⟩
  · rintro x y z ⟨φ, hφs, hφt⟩ ⟨ψ, hψs, hψt⟩
    obtain ⟨χ, hχt, hχs⟩ := hE.trans T ψ φ (hψs.trans hφt.symm)
    exact ⟨χ, hχs.trans hφs, hχt.trans hψt⟩

lemma finiteProjective_invariantRing_quotient
    [Module.Finite B C] [Module.Projective B C]
    (hE : RingEtaleEquivalenceRelation t)
    (ht : letI := t.toAlgebra; Module.Finite B C)
    (ht' : letI := t.toAlgebra; Module.Projective B C) :
    Module.Finite (invariantRing t) B ∧
      Module.Projective (invariantRing t) B ∧
      Module.FaithfullyFlat (invariantRing t) B ∧
      IsPushout (CommRingCat.ofHom (algebraMap (invariantRing t) B))
        (CommRingCat.ofHom (algebraMap (invariantRing t) B))
        (CommRingCat.ofHom (algebraMap B C)) (CommRingCat.ofHom t) := by
  refine FiniteLocallyFreeQuotient.invariantRingQuotient (algebraMap B C) t
    (by rw [toAlgebra_algebraMap]; infer_instance)
    (by rw [toAlgebra_algebraMap]; infer_instance)
    ht ht' hE.range_sup_eq_top hE.source_target_equivalence
    (fun x y h => Subtype.ext h) ?_
  intro b
  constructor
  · intro hb
    exact ⟨⟨b, hb.symm⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact a.property.symm

/-- A finite projective relation is the tensor square over its invariant ring. -/
noncomputable def finiteProjectiveTensorEquiv
    [Module.Finite B C] [Module.Projective B C]
    (hE : RingEtaleEquivalenceRelation t)
    (ht : letI := t.toAlgebra; Module.Finite B C)
    (ht' : letI := t.toAlgebra; Module.Projective B C) :
    C ≃ₐ[B] B ⊗[invariantRing t] B := by
  let h := (hE.finiteProjective_invariantRing_quotient ht ht').2.2.2
  let h' := CommRingCat.isPushout_tensorProduct (invariantRing t) B B
  let e := h.isoIsPushout _ _ h'
  refine { e.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro b
  exact congrArg
    (fun f : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[invariantRing t] B) => f b)
    (IsPushout.inl_isoIsPushout_hom _ _ h h')

@[simp]
lemma finiteProjectiveTensorEquiv_source
    [Module.Finite B C] [Module.Projective B C]
    (hE : RingEtaleEquivalenceRelation t)
    (ht : letI := t.toAlgebra; Module.Finite B C)
    (ht' : letI := t.toAlgebra; Module.Projective B C) (b : B) :
    hE.finiteProjectiveTensorEquiv ht ht' (algebraMap B C b) =
      b ⊗ₜ[invariantRing t] (1 : B) :=
  (hE.finiteProjectiveTensorEquiv ht ht').commutes b

@[simp]
lemma finiteProjectiveTensorEquiv_target
    [Module.Finite B C] [Module.Projective B C]
    (hE : RingEtaleEquivalenceRelation t)
    (ht : letI := t.toAlgebra; Module.Finite B C)
    (ht' : letI := t.toAlgebra; Module.Projective B C) (b : B) :
    hE.finiteProjectiveTensorEquiv ht ht' (t b) =
      (1 : B) ⊗ₜ[invariantRing t] b := by
  let h := (hE.finiteProjective_invariantRing_quotient ht ht').2.2.2
  let h' := CommRingCat.isPushout_tensorProduct (invariantRing t) B B
  exact congrArg
    (fun f : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[invariantRing t] B) => f b)
    (IsPushout.inr_isoIsPushout_hom _ _ h h')

end Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelation
