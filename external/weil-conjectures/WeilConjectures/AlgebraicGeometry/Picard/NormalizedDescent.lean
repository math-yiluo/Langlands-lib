/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Descent
public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.DescentData
public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.DescentDataModules
public import WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent.Modules

/-!
# Descent data for invertible modules normalized along a section

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.Picard.NormalizedDescent`; it was split to keep the
compilation of each part cheap.

Let `f: X ⟶ S` be a morphism of schemes and let `s` choose, for every scheme `Y` over `S`, a
section `s Y` of the projection `X_Y = X ×_S Y ⟶ Y`. Let `{T i ⟶ T}` be a family of schemes over
`S` and `L i` invertible modules on `X_{T i}` whose pullbacks along the sections are trivialised
by isomorphisms `α i: (s (T i))^* L i ≅ (T i ⟶ T)^* N`. A morphism between pullbacks of the
`L i` is *normalized* if its pullback along the section is compatible with the trivialisations.

When `Γ(Y, 𝒪_Y) ⟶ Γ(X_Y, 𝒪_{X_Y})` is surjective, normalized morphisms are unique, and any
isomorphism can be rescaled by a unit to a normalized one. Consequently normalized gluing
isomorphisms automatically satisfy the cocycle condition. This is the rigidification in the proof
that the `σ`-normalized relative Picard functor is an fppf sheaf.

## Main definitions

- `AlgebraicGeometry.IsSectionNormalized`: the normalization condition on a morphism.
- `AlgebraicGeometry.chosenPullbackBaseChangeMap`, `AlgebraicGeometry.chosenPullback₃BaseChangeMap`:
  the fibre products `X_{A ×_C B}` of `X_A ⟶ X_C ⟵ X_B`, and the triple fibre products, in terms
  of which descent data are written down.
- `AlgebraicGeometry.descentDataOfIsSectionNormalized`: normalized gluing isomorphisms form a
  descent datum, for any pseudofunctor in which normalized morphisms are rigid.
- `AlgebraicGeometry.normalizedDescentData`: the descent datum of sheaves of modules obtained by
  normalizing gluing isomorphisms.

## Main statements

- `AlgebraicGeometry.IsSectionNormalized.eq`: rigidity of normalized morphisms.
- `AlgebraicGeometry.exists_isSectionNormalized`: every isomorphism can be normalized.
-/
