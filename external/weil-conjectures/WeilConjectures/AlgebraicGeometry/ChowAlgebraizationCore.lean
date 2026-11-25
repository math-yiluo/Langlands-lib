/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationCompactificationData
import WeilConjectures.AlgebraicGeometry.ChowAlgebraizationCoreSupport

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraization on the supplied quasi-projective modification with proper support on Y.
Source: Stacks Project, Theorem 088E, the projective compactification argument
(https://stacks.math.columbia.edu/tag/088E), using Tags 0885, 0CYJ, and 0CYQ.
(blueprint: new-chow-algebraization-core)

Proof: Properness of q makes Y Noetherian. Factor the quasi-compact immersion e as
an open immersion j into its scheme-theoretic image Y', a closed subscheme of the
supplied projective space. Pull G back using exists_formalSystemsPullback. Nakayama and
compatibility of successive quotients identify the supports of all pulled terms with
the inverse image of the degree-zero support. By hR and properness of q this set is
proper over A. Its image under j is closed in Y'. Extend the pulled terms by j_*;
coherence follows from pushforward_coherent_on_open. On j(Y) quotient compatibility
is unchanged, and off the closed support all terms vanish, so the extended terms
form a coherent formal system. Projective existence algebraizes it to F' on Y'.
Nakayama identifies its support over V(I) with the degree-zero support. The boundary
part of Supp(F') is closed in the proper Y', so its image in Spec A is closed. If
nonempty it meets V(I), since I is in the Jacobson radical of the complete ring A,
contradicting the degree-zero support calculation. Thus Supp(F') lies inside j(Y).
Restrict F' to Y. Its completion is the pulled system by the restriction/completion
comparison; its support is the transport of the proper closed support of F'. -/
theorem exists_chow_algebraization_core
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
      q ≫ f) :
    ∃ F : CoherentModules Y,
      Nonempty (G.obj ⋙ Scheme.Modules.tensorPullback q ≅
        formalCompletionSystem (Q.comap q) F.obj) ∧
      Scheme.Modules.HasSupportProperOver (q ≫ f) F.obj := by
  obtain ⟨P, p, j, F', F, hP, hp, hj, hcomp, heF, hF, hs⟩ :=
    exists_chow_algebraization_compactification_data A I f Q hQ G hR Y q n e he
  have : IsNoetherian P := hP
  obtain ⟨eF⟩ := heF
  refine ⟨F, hF, ?_⟩
  have h := chow_algebraization_candidate_support A I p j F' F eF hs
  simpa only [hcomp] using h

end AlgebraicGeometry
