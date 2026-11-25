/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ChowModificationData
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationData
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Algebraization of the pullback along a Chow modification

Source: Stacks Project, Theorem 088E, projective compactification argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The pullback of a properly supported formal system to a Chow modification
algebraizes. The coherent pushforward of this algebraization has proper support.
The open locus on which the modification is an isomorphism is explicitly nonempty.

Source: Stacks Project, Theorem 088E, paragraphs 2--4, using Lemmas 0885 and 0887.
(blueprint: lem-weil-pbc-chow-pullback-algebraization).

Proof: Apply Chow's lemma to f. On its nonempty dense isomorphism locus U, let L
be the ideal of the reduced closed complement. Its support complement is U.
The modification q is proper and its source Y is Noetherian. The quasi-projective
immersion of Y is quasi-compact: Y is quasi-compact and the projective target is
quasi-separated. Its scheme image gives a projective closure Y' with Y open in Y'.
Termwise tensor pullback is coherent formal and the support of its first term is
the inverse image of the first support of G. Nakayama identifies the later supports
with this one. Properness is preserved under the proper modification. Its image
in separated Y' is closed and proper. Extend the pulled system by zero to Y':
on Y this is the original coherent system, and on the complement of its closed
support it is zero. These opens cover Y', proving coherence and the adic quotient
conditions locally. Projective existence algebraizes it on Y'. The part of the
algebraization's support outside Y is closed in the proper Y' and hence has closed
image in Spec A. If nonempty, that image meets V(I), since I is in the Jacobson
radical of an I-adically complete ring. Nakayama would then put a point outside Y
in the support of the extended first term, a contradiction. Restrict the resulting
coherent module to Y to obtain F and the completion isomorphism beta. Its support
is proper over A. Proper coherent pushforward has support contained in its closed
image under q; that image is proper over A, and closed subsets of it are proper.
This proves the last support assertion. The isomorphism beta is essential: F is
an algebraization of this particular pulled system, not an arbitrary module. -/
theorem exists_chowPullbackAlgebraization
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (hZ : Nonempty Z) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Z) (_ : IsProper q) (L : Z.IdealSheafData)
      (F : CoherentModules Y),
      (L.support.compl : Set Z).Nonempty ∧
      IsIso (pullback.snd q (Scheme.Opens.ι L.support.compl)) ∧
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      Scheme.Modules.HasSupportProperOver f ((Scheme.Modules.pushforward q).obj F.obj)
      := by
  obtain ⟨Y, q, hq, L, n, e, heImm, he, hL, hIso⟩ :=
    exists_chow_modification_data A f hZ
  have : IsProper q := hq
  have : IsImmersion e := heImm
  obtain ⟨F, hF, hSupp⟩ :=
    exists_chow_algebraization_data A I f Q hQ G hR Y q n e he L hL hIso
  exact ⟨Y, q, hq, L, F, hL, hIso, hF, hSupp⟩

end AlgebraicGeometry
