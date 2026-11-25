/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Ulift

import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.EpiMono

/-! Coefficient universe lift on the small étale site. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Coefficient lift preserves homology of abelian sheaves on the small étale site.
Source: step 3 of lem-sc-etale-ulift-injective-resolution; Mathlib
`AddCommGrpCat.uliftFunctor`, `Sheaf.isLocallySurjective_iff_epi'`, and
`Functor.preservesHomology_of_preservesEpis_and_kernels`.
(blueprint: lem-sc-etale-ulift-homology)

Proof: Coefficient lift is additive since it acts on morphisms objectwise by ULift.
Kernels of abelian sheaves are computed objectwise, and the group lift functor preserves
kernels. Epimorphisms of abelian sheaves are locally surjective. A local preimage of a
section before lift gives a local preimage after lift by up, and conversely down gives
the same local lifting condition. Thus coefficient lift preserves epimorphisms.
An additive functor between abelian categories preserving kernels and epimorphisms
preserves short exact sequences, hence is exact and preserves homology. Equivalently,
apply Mathlib's preservation-of-homology criterion for exact additive functors. Zero
objects and zero complexes are included; no affine or nonemptiness assumption is used. -/
theorem etale_ulift_preservesHomology (X : Scheme.{u}) :
    (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesHomology := by
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.Additive := { map_add := fun {_ _ _ _} => rfl }
  have : PreservesLimitsOfShape WalkingParallelPair L := by
    have : PreservesLimitsOfShape WalkingParallelPair
        (L ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
      change PreservesLimitsOfShape WalkingParallelPair
        (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u})
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves L
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  have : L.PreservesEpimorphisms :=
    { preserves := by
        intro A B f hf
        have : Sheaf.IsLocallySurjective f :=
          (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f).mpr hf
        have : Sheaf.IsLocallySurjective (L.map f) := by
          constructor
          intro U s
          have h := Presheaf.imageSieve_mem X.smallEtaleTopology f.hom s.down
          convert h using 1
          ext V g
          constructor
          · rintro ⟨t, ht⟩
            exact ⟨t.down, congrArg ULift.down ht⟩
          · rintro ⟨t, ht⟩
            exact ⟨ULift.up t, congrArg ULift.up ht⟩
        infer_instance }
  exact Functor.preservesHomology_of_preservesEpis_and_kernels L

end AlgebraicGeometry.Scheme
