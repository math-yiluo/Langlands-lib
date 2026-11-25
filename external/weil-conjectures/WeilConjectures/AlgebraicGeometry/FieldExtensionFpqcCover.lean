/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc cover from a field extension

Source: Stacks Project, Topologies, Definition 34.9.1 (Tag 022B) and Lemma 34.9.2
(Tag 03L7); Algebra, Definition 10.39.1 (Tag 00HB)
(blueprint: lem-pc-field-extension-fpqc-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-field-extension-fpqc-cover) For a field extension `K/k`, the
structure map `Spec K ⟶ Spec k` is flat, surjective, and quasi-compact, and its
singleton presieve is an fpqc covering (Stacks, Tags 022B, 03L7, 00HB).

First, `lem-pc-field-extension-flat` gives flatness of the spectrum map, via
`Flat.SpecMap_iff`. Second, `lem-pc-field-extension-surjective` uses the unique
points of the two spectra to give surjectivity. Third,
`lem-pc-field-extension-quasi-compact` observes that the inverse image of the
only nonempty affine open in `Spec k` is the quasi-compact `Spec K`. Finally,
`def-weil-pbc-fpqc-covering` applies: choose `Spec K` over the nonempty affine
open using flatness and surjectivity, and choose no members over the empty open.
These are the clauses of the fpqc covering definition. -/
theorem fpqcCover_specMap_algebraMap_of_field
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∈
        Scheme.fpqcPrecoverage (Spec (.of k)) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

end AlgebraicGeometry
