/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteCoordinates
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProjective
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Algebraization after a projective modification

Source: Stacks Project, Proposition 088C, last paragraph, using Tags 0200, 0887 and 0885.
(blueprint: lem-weil-pbc-proper-existence-projective-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A coherent formal system on a proper scheme algebraizes after a proper modification
which is an isomorphism over a dense open. Only the pulled-back system is algebraized.
Source: Stacks Project, Proposition 088C, last paragraph, using Tags 0200, 0887 and 0885.
(blueprint: lem-weil-pbc-proper-existence-projective-pullback).

Proof:
1. Apply Chow's lemma to f to obtain q:Y -> X proper and surjective, an isomorphism over
some dense open U, and an immersion of Y into projective space over Spec A with finite
homogeneous index set. Both X and Y are Noetherian by finite type over the Noetherian base.
The composite Y -> Spec A is proper. Since projective space is separated over Spec A,
the immersion into it is proper, hence closed.
2. The existing finite-coordinate theorem embeds that projective space as a closed linear
subscheme of one indexed by ULift(Fin(n+1)), preserving its base projection. It uses a
surjective graded polynomial-ring map with one extra coordinate sent to zero, so also
handles an empty coordinate type. Compose Chow's closed immersion with this embedding.
3. Formal-systems pullback (Tag 0887) makes the termwise tensor pullback of M a coherent
formal module on Y for J.comap q. Functoriality of comap identifies this with the ideal
extended from I along q followed by f.
4. Apply projective existence (Tag 0885) to the closed embedding. Essential surjectivity
gives coherent F and a completion isomorphism with the pulled-back formal module.
Apply the full-subcategory inclusion and reverse the isomorphism. The defining inclusion
equation of the pullback functor identifies its object with M.obj followed by tensor
pullback, giving exactly beta. The construction uses no algebraization on X or induction. -/
theorem proper_existence_projective_pullback
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (M : CoherentFormalModule X
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)) :
    let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X) (_ : IsProper q) (U : X.Opens),
      Dense (U : Set X) ∧ IsIso (q ∣_ U) ∧
      ∃ F : CoherentModules Y,
        Nonempty (M.obj ⋙ Scheme.Modules.tensorPullback q ≅
          formalCompletionSystem (J.comap q) F.obj) := by
  classical
  let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f
  let Y := ChowModification f
  let q := ChowModification.modificationMap f
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (q ≫ f)
  obtain ⟨n, k, hk, hw⟩ := ProjectiveSpace.exists_isClosedImmersion_finite_coordinates
    (ChowModification.index f) (Spec (CommRingCat.of A))
  let := hk
  let i := ChowModification.toProjectiveSpace f ≫ k
  have hover : i ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A) =
      q ≫ f := by
    dsimp only [i]
    rw [Category.assoc, hw, ChowModification.toProjectiveSpace_over]
  have heq : (completion Y (J.comap q)).IsEquivalence := by
    have h := completion_isEquivalence_of_projective_embedding A I Y n i
    change Functor.IsEquivalence (completion Y
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
        (i ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A))))
      at h
    rw [hover, Scheme.IdealSheafData.comap_comp] at h
    exact h
  let := heq
  obtain ⟨P, C, hP, _, _⟩ := (exists_formalSystemsPullback q J).1
  let F := (completion Y (J.comap q)).objPreimage (P.obj M)
  let e := (completion Y (J.comap q)).objObjPreimageIso (P.obj M)
  obtain ⟨U, hU, hqU⟩ := ChowModification.exists_dense_isIso_restrict f
  refine ⟨Y, q, inferInstance, U, hU, hqU, F, ?_⟩
  have he : (P.obj M).obj ≅ formalCompletionSystem (J.comap q) F.obj :=
    (ObjectProperty.ι (IsCoherentFormalModule (J.comap q))).mapIso e.symm
  have hobj : (P.obj M).obj = M.obj ⋙ Scheme.Modules.tensorPullback q :=
    congrArg (fun T ↦ T.obj M) hP
  exact ⟨(eqToIso hobj).symm ≪≫ he⟩

end AlgebraicGeometry
