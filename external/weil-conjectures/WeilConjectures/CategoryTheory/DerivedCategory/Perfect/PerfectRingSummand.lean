/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.Basic

/-!
# Direct summands of perfect complexes over a ring

Source: Stacks Project, More on Algebra, Tag 066S, `lemma-summands-perfect`
(blueprint: lem-sf-perfect-ring-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- If the binary direct sum of two objects of `D(A)` is perfect, both objects are perfect.
Source: Stacks Project, More on Algebra, Tag 066S, `lemma-summands-perfect`
(blueprint: lem-sf-perfect-ring-summand).

Proof:
1. Choose a bounded finite-projective model P for K ⊞ L. Replace P by a bounded-above
   finite-free model using `exists_finiteFree_model_of_finite_projective`. Its derived
   isomorphism exhibits pseudo-coherence of K ⊞ L. Apply `pseudoCoherent_summand` to
   obtain pseudo-coherence of K and L.
2. The terms of P are flat because they are projective. Apply the proved generic
   `torAmplitudeIn_Q_obj_of_flat` to P and transport the resulting Tor bound across
   the model isomorphism. Enlarge [a, b] to [min a b, b], whose endpoints are ordered
   even if the original witness has a > b (and hence represents the zero complex).
3. The inclusion and projection of each biproduct summand give a retract. The existing
   stability of `torAmplitudeIn` under retracts transfers this common Tor interval to
   K and L. This is the tensor/cohomology retract argument of Stacks Tag 066G.
4. Apply `isPerfect_of_pseudoCoherent_finiteTorAmplitude` to each summand. Its bounded
   finite-projective model satisfies the strict lower and upper support predicates
   by `isStrictlyGE_iff` and `isStrictlyLE_iff`, giving exactly the required perfectness.
No Noetherian hypothesis is used. -/
theorem isPerfectRingComplex_summand {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (K L : DerivedCategory (ModuleCat.{u} A)) (h : IsPerfectRingComplex (K ⊞ L)) :
    IsPerfectRingComplex K ∧ IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h
  have : P.IsStrictlyGE a := ha
  have : P.IsStrictlyLE b := hb
  obtain ⟨F, hFb, hF, f, hf⟩ :=
    CochainComplex.exists_finiteFree_model_of_finite_projective A P b hb
      (fun i => (hP i).2) (fun i => (hP i).1)
  have : QuasiIso f := hf
  have hPC : IsPseudoCoherent (K ⊞ L) :=
    ⟨F, b, hFb, hF, ⟨asIso (Q.map f) ≪≫ e.symm⟩⟩
  obtain ⟨hK, hL⟩ := pseudoCoherent_summand K L hPC
  have hflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
    have := (hP i).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hTor : torAmplitudeIn (ModuleCat.{u} A) (min a b) b (K ⊞ L) := by
    apply (torAmplitudeIn (ModuleCat.{u} A) (min a b) b).prop_of_iso e.symm
    exact (torAmplitudeIn_Q_obj_of_flat P a b hflat).mono (min_le_left _ _) le_rfl
  have hTorK : torAmplitudeIn (ModuleCat.{u} A) (min a b) b K :=
    (torAmplitudeIn (ModuleCat.{u} A) (min a b) b).prop_of_retract
      (show Retract K (K ⊞ L) from ⟨biprod.inl, biprod.fst, biprod.inl_fst⟩) hTor
  have hTorL : torAmplitudeIn (ModuleCat.{u} A) (min a b) b L :=
    (torAmplitudeIn (ModuleCat.{u} A) (min a b) b).prop_of_retract
      (show Retract L (K ⊞ L) from ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩) hTor
  have finish (T : DerivedCategory (ModuleCat.{u} A)) (hT : IsPseudoCoherent T)
      (hTorT : torAmplitudeIn (ModuleCat.{u} A) (min a b) b T) :
      IsPerfectRingComplex T := by
    obtain ⟨E, ⟨c, d, hE⟩, hfin, hproj, ⟨eT⟩⟩ :=
      isPerfect_of_pseudoCoherent_finiteTorAmplitude T hT
        ⟨min a b, b, min_le_right _ _, hTorT⟩
    exact ⟨E, c, d, (E.isStrictlyGE_iff c).2 (fun i hi => hE i (Or.inl hi)),
      (E.isStrictlyLE_iff d).2 (fun i hi => hE i (Or.inr hi)),
      fun i => ⟨hproj i, hfin i⟩, ⟨eT.symm⟩⟩
  exact ⟨finish K hK hTorK, finish L hL hTorL⟩

end DerivedCategory
