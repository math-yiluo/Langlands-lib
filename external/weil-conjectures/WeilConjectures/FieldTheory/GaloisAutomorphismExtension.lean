/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Extending an automorphism of a separable closure

Source: Stacks Project, Tag 03QW, discussion of the action on geometric stalks.
-/

@[expose] public section

universe u

/-- Source: Stacks Project, Tag 03QW, construction of the Galois action on stalks.
(blueprint: lem-exc-galois-automorphism-extension).

Proof: The algebraic closure of K inside Omega is an algebraic closure of Ks.
Extend g to an automorphism of it by the extension theorem for embeddings into
an algebraic closure; the resulting endomorphism is surjective because this is
an algebraic normal extension. Choose a transcendence basis of Omega over this
algebraic closure. Acting on coefficients and fixing the basis gives an
isomorphism of the rational function field. Omega is its algebraic closure,
so this isomorphism extends to an automorphism of Omega. It fixes K, agrees
with g on the embedded Ks, and hence has the asserted restriction. If Omega
is algebraic over K, the transcendence basis is empty and the first extension
already gives the result. The argument works in positive characteristic too:
the purely inseparable part of the algebraic closure has unique extensions. -/
theorem exists_algEquiv_extending_separableClosure
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] (g : Gal(Ks/K)) :
    ∃ τ : Ω ≃ₐ[K] Ω,
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis Ks Ω
  let A := Algebra.adjoin Ks (Set.range ((↑) : B → Ω))
  let e : MvPolynomial B Ks ≃ₐ[Ks] A := hB.1.aevalEquiv
  let f : A ≃+* A := e.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv B g.toRingEquiv).trans e.toRingEquiv)
  have : IsAlgClosure A Ω :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis ((↑) : B → Ω) hB
  let t : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω f
  have hf (x : Ks) : f (algebraMap Ks A x) = algebraMap Ks A (g x) := by
    change e (MvPolynomial.mapEquiv B g.toRingEquiv
      (e.symm (algebraMap Ks A x))) = _
    rw [e.symm.commutes]
    change e (MvPolynomial.map g.toRingHom (MvPolynomial.C x)) = _
    rw [MvPolynomial.map_C]
    exact e.commutes (g x)
  have ht (x : Ks) : t (algebraMap Ks Ω x) = algebraMap Ks Ω (g x) := by
    calc
      t (algebraMap Ks Ω x) = t (algebraMap A Ω (algebraMap Ks A x)) := by
        rw [IsScalarTower.algebraMap_apply Ks A Ω]
      _ = algebraMap A Ω (f (algebraMap Ks A x)) :=
        IsAlgClosure.equivOfEquiv_algebraMap Ω Ω f _
      _ = algebraMap Ks Ω (g x) := by
        rw [hf, ← IsScalarTower.algebraMap_apply Ks A Ω]
  let τ : Ω ≃ₐ[K] Ω :=
    { t with
      commutes' := fun x => by
        change t (algebraMap K Ω x) = algebraMap K Ω x
        rw [IsScalarTower.algebraMap_apply K Ks Ω, ht, g.commutes] }
  refine ⟨τ, ?_⟩
  ext x
  exact (ht x).symm
