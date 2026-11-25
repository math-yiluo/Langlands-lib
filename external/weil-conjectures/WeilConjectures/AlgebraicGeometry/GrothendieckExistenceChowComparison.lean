/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ClosedQuotientFormalPresentation
import WeilConjectures.AlgebraicGeometry.ChowPullbackAlgebraization
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFormalComparisonTransport
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPull

/-! # The Chow comparison on a closed quotient

Source: Stacks Project, Cohomology of Schemes, Theorem 088E, paragraphs 2--4.
(blueprint: lem-weil-pbc-grothendieck-existence-chow-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A formal module killed by K without proper scheme-theoretic support admits a comparison
to a properly supported formal module whose kernel is killed
by a strictly larger ideal. This is the geometric part of the Noetherian induction;
it does not assume or conclude proper scheme-theoretic support for that kernel.

Source: Stacks Project, Cohomology of Schemes, Theorem 088E, paragraphs 2--4.
(blueprint: lem-weil-pbc-grothendieck-existence-chow-comparison).

Proof:
1. Replace X by V(K). The closed-immersion coherent-formal equivalence identifies M
with the pushforward of a coherent formal module there, preserving first support.
V(K) is nonempty: otherwise the system is zero and is supported on the empty proper
subscheme, contradicting the hypothesis.
2. Chow's lemma gives a proper modification q:Y -> V(K), an isomorphism
on a nonempty dense open U, and an immersion e into a finite projective space.
The immersion e is quasi-compact because Y is quasi-compact and projective space
is quasi-separated. Set Y' := e.image and use e.toImage:Y -> Y' and e.imageι.
The former is open and the latter closed by the scheme-image factorization for
a quasi-compact immersion. Thus Y' is projective over A.
Tensor pullback of the system is coherent. Nakayama identifies all its supports
with the pullback of the first support. This support is proper over A, hence its
image in the separated Y' is closed. Extend the system by zero to Y'; coherence
and the adic quotient conditions hold locally on Y and the complement of that support.
3. Projective existence algebraizes the extended system. Its support lies in Y:
otherwise its closed complement has nonempty closed image in Spec A, which meets
V(I) since I is in the Jacobson radical of the complete ring. Reduction modulo I
and Nakayama contradict the support of the extended first term. Restrict to Y.
4. Proper pushforward of this algebraization is a coherent module H on V(K).
Its support lies in the image of a proper support on Y, so is proper. The
scheme-theoretic support of H is proper and kills H and all its adic quotients.
Push its completion to X; call this formal module N. Its supporting closed
subscheme remains closed in X and proper over A.
5. The push-pull comparison on V(K) gives alpha to the completion of H. Its formal
kernel is killed by a positive power L^t of the ideal of V(K) minus U. This power
is nonzero because its restriction to the nonempty U is the unit ideal. The
inverse image J of L^t under O_X -> O_V(K) strictly contains K. Exactness of the
closed pushforward equivalence identifies the pushed kernel with kernel alpha,
and J kills it. This yields the asserted comparison. No induction is used here. -/
theorem grothendieckExistence_chow_comparison
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    let Q := (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
    ∀ [Abelian (CoherentFormalModule X Q)] (K : X.IdealSheafData)
      (M : CoherentFormalModule X Q),
      AnnihilatedBy Q K M →
      Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)) →
      (¬ ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
        IsProper (j ≫ f) ∧ AnnihilatedBy Q j.ker M) →
      ∃ (N : CoherentFormalModule X Q) (α : M ⟶ N) (J : X.IdealSheafData),
        K < J ∧ AnnihilatedBy Q J (kernel α) ∧
        ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j),
          IsProper (j ≫ f) ∧ AnnihilatedBy Q j.ker N := by
  intro Q _ K M hK hR hP
  let j := K.subschemeι
  let : IsNoetherian K.subscheme := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨G, ⟨e⟩, hG, hZ⟩ :=
    exists_closedQuotientFormalPresentation f Q K M hK hR hP
  have hQ : Q.comap j = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap (j ≫ f) := by
    exact (Scheme.IdealSheafData.comap_comp
      (Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) j f).symm
  obtain ⟨Y, q, hq, L, F, hU, hV, ⟨β⟩, hF⟩ :=
    exists_chowPullbackAlgebraization A I (j ≫ f) (Q.comap j) hQ G hG hZ
  let : IsProper q := hq
  obtain ⟨hcoh, α, t, k, c, ht, ⟨hk⟩, _, hkill, _⟩ :=
    exists_formalSystemsPushPull (Q.comap j) L q hV G F β
  obtain ⟨N, a, J, hJ, hker, hN⟩ :=
    exists_closedImmersionFormalComparisonTransport f j Q M G e
      ⟨(Scheme.Modules.pushforward q).obj F.obj, hcoh⟩ hF L hU α t ht k hk hkill
  refine ⟨N, a, J, ?_, hker, hN⟩
  simpa only [j, Scheme.IdealSheafData.ker_subschemeι] using hJ

end AlgebraicGeometry
