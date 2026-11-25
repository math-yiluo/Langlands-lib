/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma

/-!
# A projective modification of a proper scheme

Over a Noetherian base `S`, a proper `X ⟶ S` is dominated by a projective `S`-scheme through a
proper morphism which is an isomorphism over a dense open subset of `X`
(`AlgebraicGeometry.exists_projective_modification`, blueprint
`theorem-chow-s-lemma-projective-form--1`). This is Chow's lemma
(`AlgebraicGeometry.ChowModification`) for proper morphisms.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `theorem-chow-s-lemma-projective-form--1`: A projective modification of a reduced
proper scheme.

Let `S` be Noetherian and `f : X ⟶ S` proper. There are a proper map `π : Y ⟶ X` and a dense open
`U ⊆ X` such that `π⁻¹(U) ⟶ U` is an isomorphism and `Y ⟶ S` is projective: `π ≫ f` factors as
a closed immersion `e : Y ⟶ ℙ(N; S)` followed by the structure morphism, for a finite index type
`N` of homogeneous coordinates. The blueprint takes `S` affine and `X` reduced; neither is
needed. The modification is moreover surjective. -/
theorem exists_projective_modification {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [IsProper f] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (U : X.Opens), IsProper π ∧ Surjective π ∧
      Dense (U : Set X) ∧ IsIso (π ∣_ U) ∧
      ∃ (N : Type u) (_ : Finite N) (e : Y ⟶ ℙ(N; S)), IsClosedImmersion e ∧
        e ≫ ℙ(N; S) ↘ S = π ≫ f := by
  obtain ⟨U, hU, hiso⟩ := ChowModification.exists_dense_isIso_restrict f
  exact ⟨_, ChowModification.modificationMap f, U, inferInstance, inferInstance, hU, hiso,
    ChowModification.index f, inferInstance, ChowModification.toProjectiveSpace f,
    inferInstance, ChowModification.toProjectiveSpace_over f⟩

end AlgebraicGeometry
