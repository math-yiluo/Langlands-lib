/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing

/-!
# Sections of separated étale morphisms

A section `s` of a separated étale morphism `g : U ⟶ X` is an open and closed immersion: it is
a monomorphism and étale (as a morphism between étale `X`-schemes), hence an open immersion,
and it is a closed immersion because `g` is separated. Consequently `U` splits as the disjoint
union of the image of `s` and the complementary open subscheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (s : X ⟶ U) (hs : s ≫ g = 𝟙 X)

include hs in
/-- A section of an étale morphism is an open immersion. -/
lemma IsOpenImmersion.of_section_of_etale : IsOpenImmersion s := by
  have : Etale (s ≫ g) := by rw [hs]; infer_instance
  have : Etale s := Etale.of_comp s g
  have : Mono s := mono_of_mono_fac hs
  exact IsOpenImmersion.of_etale_of_universallyInjective s

omit [Etale g] in
include hs in
/-- A section of a separated morphism is a closed immersion. -/
lemma IsClosedImmersion.of_section_of_isSeparated [IsSeparated g] : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s g

omit [Etale g] in
include hs in
/-- The complement of the image of a section of a separated étale morphism is open. -/
lemma isOpen_compl_range_of_section [IsSeparated g] : IsOpen (Set.range s.base)ᶜ :=
  (IsClosedImmersion.of_section_of_isSeparated g s hs).isClosedEmbedding.isClosed_range.isOpen_compl

include hs in
/-- The image of a section of a separated étale morphism and its complement are complementary
open subsets. -/
lemma isCompl_opensRange_of_section [IsSeparated g] :
    haveI := IsOpenImmersion.of_section_of_etale g s hs
    IsCompl s.opensRange ⟨(Set.range s.base)ᶜ, isOpen_compl_range_of_section g s hs⟩ := by
  have := IsOpenImmersion.of_section_of_etale g s hs
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor <;> ext x <;> simp

end AlgebraicGeometry
