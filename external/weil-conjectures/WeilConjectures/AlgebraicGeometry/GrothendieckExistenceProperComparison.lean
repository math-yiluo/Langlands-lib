/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProjectivePullback
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPull

/-! # Projective-modification comparison for proper algebraization

Source: Stacks Project, Proposition 088C, last paragraph, and Lemma 088B.
(blueprint: lem-weil-pbc-proper-existence-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A formal module on a nonempty proper scheme compares with a completed coherent module.
The error is killed by a power of an ideal all of whose positive powers are nonzero.
This statement does not assume algebraization on any closed subscheme.
Source: Stacks Project, Proposition 088C, last paragraph, and Lemma 088B.
(blueprint: lem-weil-pbc-proper-existence-comparison).

Proof:
1. Apply Chow's lemma (Tag 0200) to f. Its proper surjective modification q:Y -> X
is an isomorphism on a dense open U. Since X is nonempty, U is nonempty. The immersion
of Y into finite projective space is closed: its composite to Spec A is proper and
projective space is separated over Spec A. The finite-coordinate embedding theorem
puts Y in standard projective space, including an empty homogeneous index set.
2. Let K be the radical ideal of the reduced complement X minus U. Its support is that
complement. For every e >= 1 the support of K^e equals the support of K, and misses U.
The zero ideal has support all of X, so K^e is nonzero. This includes U = X: K is then
the unit ideal, whose powers are nonzero on a nonempty scheme.
3. Pull M back along q using formal-systems pullback (Tag 0887). Projective existence
(Tag 0885) gives a coherent F on Y and an isomorphism q^*M to its completion. The ideal
on Y is the extension of I along q followed by f, by functoriality of ideal comap.
The pullback functor's inclusion equation gives the same isomorphism in the ambient
inverse-system category, as required by the push-pull theorem.
4. Apply formal-systems push-pull (Tag 088B) to q, K, F and that isomorphism. It gives
coherence of H = q_*F, a map alpha:M -> H-completion, and a positive exponent t killing
the kernel and cokernel. Kernel forks, cokernel coforks and their universal properties
are exactly those furnished by that theorem. Together with step 2 these are the claim. -/
theorem proper_existence_comparison
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} [IsNoetherian X] [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (M : CoherentFormalModule X
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)) :
    let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f
    ∃ K : X.IdealSheafData,
      (∀ e : ℕ, 1 ≤ e → K ^ e ≠ ⊥) ∧
      ∃ (H : CoherentModules X) (α : M ⟶ (completion X J).obj H),
        ∃ t : ℕ, 1 ≤ t ∧
          ∃ k : KernelFork α, ∃ c : CokernelCofork α,
            Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧
            (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower K.toModulesι t).2 (k.pt.obj.obj (op n)))) ∧
            (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower K.toModulesι t).2 (c.pt.obj.obj (op n)))) := by
  classical
  let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f
  obtain ⟨Y, q, hq, U, hU, hqU, F, ⟨β⟩⟩ :=
    proper_existence_projective_pullback A I f M
  let := hq
  let := hqU
  let K := Scheme.IdealSheafData.vanishingIdeal U.compl
  have hs : K.support = U.compl := by
    apply TopologicalSpace.Closeds.ext
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal U.compl
  have hK : ∀ e : ℕ, 1 ≤ e → K ^ e ≠ ⊥ := by
    intro e he hzero
    have hsupport := Scheme.IdealSheafData.support_pow K e (by omega)
    rw [hzero, Scheme.IdealSheafData.support_bot, hs] at hsupport
    obtain ⟨x, hx⟩ := hU.nonempty
    have hmem : x ∈ U.compl := by rw [← hsupport]; trivial
    exact hmem hx
  have hV : IsIso (pullback.snd q (Scheme.Opens.ι K.support.compl)) := by
    have hKU : K.support.compl = U := by rw [hs]; exact U.compl_compl
    rw [hKU, ← pullbackRestrictIsoRestrict_hom_morphismRestrict q U]
    infer_instance
  obtain ⟨hH, α, t, k, c, ht, hk, hc, hkt, hct⟩ :=
    exists_formalSystemsPushPull J K q hV M F β
  exact ⟨K, hK, ⟨(Scheme.Modules.pushforward q).obj F.obj, hH⟩, α,
    t, ht, k, c, hk, hc, hkt, hct⟩

end AlgebraicGeometry
