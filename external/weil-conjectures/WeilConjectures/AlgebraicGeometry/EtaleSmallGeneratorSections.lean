/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSmallGenerator
import WeilConjectures.AlgebraicGeometry.EtaleSmallGeneratorSectionsAux

/-!
# Section-size bound for the affine etale generator

Source: Stacks Project, Tags 01DO and 03EW; Mathlib free-Yoneda sheaves and
affine etale site comparison.
(blueprint: lem-sc-etale-small-generator-sections)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every section group of the concrete etale generator is small in the scheme universe.
Source: Stacks Project, Tag 01DO, its sheafified free representables, and the small
model of the affine etale site in Mathlib.AlgebraicGeometry.Sites.AffineEtale.
(blueprint: lem-sc-etale-small-generator-sections)

Proof: apply the surjective small-model presentation from
`etaleSmallGenerator_sections_surjective`, then use `small_of_surjective`.
-/
theorem etaleSmallGenerator_sections_small (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    Small.{u} ((etaleSmallGenerator X).obj.obj U) := by
  obtain ⟨α, f, hf⟩ := etaleSmallGenerator_sections_surjective X U
  exact small_of_surjective hf

end AlgebraicGeometry.Scheme
