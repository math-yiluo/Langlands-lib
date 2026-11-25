/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero

/-! # Closed pushforward preserves cokernels

Source: Stacks Project, Sheaves, Lemma 00AE; Modules, Lemma 01AG; Modules on Sites,
Lemma 03DA. This supplies the exactness used in the proof of Lemma 088A.
(blueprint: lem-weil-pbc-closed-immersion-pushforward-cokernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Closed pushforward preserves the cokernel of any module morphism.
Source: Stacks Project, Sheaves, Lemma 00AE; Modules, Lemma 01AG; Modules on Sites,
Lemma 03DA. The following stalk argument writes out closed-direct-image exactness,
as used in Cohomology of Schemes, proof of Lemma 088A, lines 6961--6968.
(blueprint: lem-weil-pbc-closed-immersion-pushforward-cokernel).

Proof: The underlying map of a closed immersion is a closed embedding. At a point in
its image the stalk of the direct image is the original stalk, with scalars restricted
along the map of local rings. Away from the image the stalk is zero: the open complement
is a neighbourhood disjoint from the source. Restriction of scalars is exact, and stalks
of module sheaves are exact and detect exactness. Hence direct image carries the exact
sequence A → B → cokernel f → 0 to an exact sequence. In an abelian category this says
that the pushed quotient projection is a cokernel of the pushed f. Equivalently, the
functor preserves the colimit of parallelPair f 0. This argument applies to all module
sheaves and needs neither quasi-coherence nor finite generation. For the empty source
all objects push forward to zero, so the assertion remains valid. -/
theorem closedImmersion_pushforward_preservesCokernel
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {A B : Z.Modules} (f : A ⟶ B) :
    PreservesColimit (parallelPair f 0) (pushforward i) := by
  classical
  let T := SheafOfModules.toSheaf X.ringCatSheaf
  let U := SheafOfModules.toSheaf Z.ringCatSheaf
  have : T.Faithful :=
    (CategoryTheory.moduleSheaves_colimits_forgetful X.ringCatSheaf).1
  have : PreservesFiniteLimits U :=
    (CategoryTheory.moduleSheaves_colimits_forgetful Z.ringCatSheaf).2.1
  have : PreservesFiniteLimits T :=
    (CategoryTheory.moduleSheaves_colimits_forgetful X.ringCatSheaf).2.1
  have : PreservesFiniteColimits U :=
    (CategoryTheory.moduleSheaves_colimits_forgetful Z.ringCatSheaf).2.2.1
  have : PreservesFiniteColimits T :=
    (CategoryTheory.moduleSheaves_colimits_forgetful X.ringCatSheaf).2.2.1
  have hex (S : ShortComplex Z.Modules) (hS : S.Exact) :
      (S.map (pushforward i)).Exact := by
    rw [← (S.map (pushforward i)).exact_map_iff_of_faithful T,
      TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    have : Functor.PreservesZeroMorphisms
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
    let V := pushforward i ⋙ T ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    change (S.map V).Exact
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      have : Functor.PreservesZeroMorphisms
          (TopCat.Sheaf.forget AddCommGrpCat.{u} Z ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z) := inferInstance
      let W := U ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} Z ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z)
      have : PreservesFiniteLimits
          (TopCat.Sheaf.forget AddCommGrpCat.{u} Z ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z) := inferInstance
      have : PreservesFiniteColimits
          (TopCat.Sheaf.forget AddCommGrpCat.{u} Z ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z) := inferInstance
      have : PreservesFiniteLimits W := comp_preservesFiniteLimits _ _
      have : PreservesFiniteColimits W := comp_preservesFiniteColimits _ _
      have iso (M : Z.Modules) : IsIso
          (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.base M.presheaf z) :=
        (closedImmersion_pushforward_stalks i i.isClosedEmbedding M).2.1 z |>.2.1
      let e (M : Z.Modules) := asIso
        (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.base M.presheaf z)
      have he : S.map V ≅ S.map W := ShortComplex.isoMk
        (e S.X₁) (e S.X₂) (e S.X₃)
        ((closedImmersion_pushforward_stalks i i.isClosedEmbedding S.X₁).2.2 _ S.f z).symm
        ((closedImmersion_pushforward_stalks i i.isClosedEmbedding S.X₂).2.2 _ S.g z).symm
      exact ShortComplex.exact_of_iso he.symm (hS.map W)
    · have : Subsingleton ((S.map V).X₂) :=
        (closedImmersion_pushforward_stalks i i.isClosedEmbedding S.X₂).1 x hx
      exact ShortComplex.exact_of_isZero_X₂ (S.map V)
        (AddCommGrpCat.isZero_of_subsingleton _)
  have : (pushforward i).PreservesHomology :=
    Functor.preservesHomology_of_map_exact (pushforward i) hex
  exact Functor.PreservesHomology.preservesCokernels f

end AlgebraicGeometry.Scheme.Modules
