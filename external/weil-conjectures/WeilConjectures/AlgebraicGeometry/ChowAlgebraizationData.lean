/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationCore
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationSupport

/-! # Algebraization on a quasi-projective proper modification

Source: Stacks Project, Theorem 088E, projective compactification argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraization on a supplied quasi-projective proper modification, with proper
support of the pushforward.

Source: Stacks Project, Theorem 088E, projective compactification and support paragraphs,
using Lemmas 0885 and 0887.
(blueprint: new-chow-algebraization-data).

Proof: The supplied immersion e, and the equation he over Spec A, give the required
quasi-projective structure on Y. Properness of q and Noetherianity of Z imply Y is
Noetherian. Thus e is quasi-compact. Its scheme-theoretic image in the supplied finite
projective space is a closed subscheme Y', projective over A, and e factors as an open
immersion j : Y → Y' followed by the closed immersion into that projective space.
Pull G back termwise along q. FormalSystemsPullback gives coherence and compatibility
with the powers and quotient transitions of Q.comap q, which hQ identifies with I O_Y.
The finite-type support pullback equality and Nakayama identify every term's support
with q⁻¹ Supp(G₀). This closed set is proper over A by properness of q and hR.
Its image under j is closed in the separated scheme Y' and proper over A.
Extend each pulled term by j_*: on j(Y) it is the original coherent term, and on the
complement of its closed support it is zero. These two opens cover Y'; coherence and
the formal quotient compatibility can be checked there. The extension therefore defines
a coherent formal I O_Y' system. Apply projective existence to the closed embedding of
Y' into the projective space specified by e, obtaining a coherent F' and its completion
isomorphism. The support of F' outside j(Y) is closed in the proper Y', so its image in
Spec A is closed. If nonempty, it meets V(I), since completeness puts I in the Jacobson
radical. At a point over V(I), Nakayama identifies support of F' with that of F'/IF',
which is the extended degree-zero term and has support contained in j(Y). This excludes
boundary support. Restrict F' along j to obtain F and restrict the completion isomorphism;
the pullback/completion comparison identifies it with the requested system isomorphism.
The support of F is proper over A because it is the support of F' transported into Y.
Proper coherent pushforward along q is coherent, with support contained in the closed
image of this support. That image is proper over A, and its closed subsets are proper,
which proves the asserted proper support of q_*F. The construction uses e and he to
obtain Y'; it does not presume a projective compactification for an arbitrary proper q. -/
theorem exists_chow_algebraization_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : Z.IdealSheafData)
    (hQ : Q = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (G : CoherentFormalModule Z Q)
    (hR : Scheme.Modules.HasSupportProperOver f (G.obj.obj (op 0)))
    (Y : Scheme.{u}) (q : Y ⟶ Z) [IsProper q] (n : ℕ)
    (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
    [IsImmersion e]
    (he : e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
      q ≫ f)
    (L : Z.IdealSheafData)
    (hL : (L.support.compl : Set Z).Nonempty)
    (hIso : IsIso (pullback.snd q (Scheme.Opens.ι L.support.compl))) :
    ∃ F : CoherentModules Y,
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      Scheme.Modules.HasSupportProperOver f ((Scheme.Modules.pushforward q).obj F.obj) := by
  have := hL
  have := hIso
  obtain ⟨F, hF, hproper⟩ := exists_chow_algebraization_core A I f Q hQ G hR Y q n e he
  refine ⟨F, hF, ?_⟩
  exact chow_algebraization_pushforward_support f q F hproper

end AlgebraicGeometry
