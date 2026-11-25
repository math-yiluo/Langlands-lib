/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- An open containing the closed fiber of a scheme proper over an adically complete
base is the whole scheme.
Source: Stacks Project, Tag 0GS2, complete Noetherian essential-surjectivity paragraph.
(blueprint: theorem-finite-etale-covers-proper-henselian--2)

Proof: Put h = g ≫ f and let C be the closed complement of W. Properness makes
h(C) closed; write it as V(K). If x belongs to C, K is contained in the prime h(x),
which is contained in a maximal ideal m. Thus m belongs to V(K), so h(t) = m for
some t in C. Completeness gives I ≤ jacobson(0), hence I ≤ m. The quotient spectrum
has image V(I), and the range of the base-changed projection Y ×_A Spec(A/I) → Y
is f⁻¹(V(I)). Therefore g(t) is in that range, and the hypothesis puts t in W,
contradicting t in C. The complement is empty, so W = ⊤. This includes empty X. -/
theorem proper_closed_fiber_open_eq_top
    {A : Type u} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsProper (g ≫ f)] (W : X.Opens)
    (hW : (g : X → Y) ⁻¹' Set.range
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : _ → _) ⊆
        (W : Set X)) : W = ⊤ := by
  classical
  apply top_unique
  intro x hx
  by_contra hxW
  let h := g ≫ f
  have hclosed : IsClosed (h '' (W : Set X)ᶜ) :=
    h.isClosedMap _ W.isOpen.isClosed_compl
  obtain ⟨K, hK⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hclosed
  have hxK : K ≤ (h x).asIdeal := by
    have : h x ∈ PrimeSpectrum.zeroLocus (K : Set A) :=
      hK ▸ Set.mem_image_of_mem h hxW
    exact this
  obtain ⟨m, hm, hxm⟩ := (h x).asIdeal.exists_le_maximal (h x).isPrime.ne_top
  let q : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hq : q ∈ h '' (W : Set X)ᶜ := by
    rw [hK]
    exact hxK.trans hxm
  obtain ⟨t, htW, htq⟩ := hq
  apply htW
  apply hW
  rw [Scheme.Pullback.range_fst]
  change f (g t) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  change I ≤ (f (g t)).asIdeal
  have hIm : I ≤ m := (IsAdicComplete.le_jacobson_bot I).trans
    ((Ideal.jacobson_mono (show (⊥ : Ideal A) ≤ m from bot_le)).trans
      (by let := hm; exact le_of_eq (Ideal.jacobson_eq_self_of_isMaximal (I := m))))
  change I ≤ (h t).asIdeal
  rw [htq]
  exact hIm

end AlgebraicGeometry
