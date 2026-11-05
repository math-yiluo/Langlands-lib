# Ordinary pullback of a specified trivialization

For arbitrary schemes `X`, `Y` and `Z` in a common universe, let
`p : Y → X`, `f : Z → Y` and `g : Z → X` be actual scheme morphisms
with a specified equality `g = f ≫ p`. For an actual scheme module `N`
on `X`, a specified trivialization of its ordinary pullback along `p`
induces `compositeUnitIso`, a trivialization of its ordinary pullback
along `g`.

The construction composes the comparison along equal scheme morphisms,
the inverse ordinary pullback composition comparison, the pulled-back
specified isomorphism, and the canonical structure-sheaf pullback
isomorphism. `compositeUnitIso_adjoint_app` computes its adjoint on every
open `U` of `X` and every section of `N` on `U`: apply the initial
adjoint, then the actual section map `f.app`, then restrict along the
equality of the two inverse-image opens.

This internal construction uses commutative rings `R`, `A` and `C` in an
arbitrary common universe, actual ring maps `φ : R → A`, `ψ : A → C`
and `χ : R → C`, and an equality `φ ≫ ψ = χ`. For an actual `R`-module
`M`, a specified ordinary pullback trivialization of its associated sheaf
over `Spec A` induces `affineCompositeUnitIso` over `Spec C`.

This affine specialization uses the general construction and the
contravariant composition identity for `Spec.map`. Its source is the
ordinary pullback along `Spec.map χ`.

`affineCompositeUnitIso_adjoint_toOpen` retains an actual specified
coordinate function `q : M → A`: if the adjoint of the initial
trivialization sends every generator on every open to the generator of
`q m`, the composite adjoint sends it to the generator of `ψ (q m)`.
No linearity premise on `q` is needed beyond the stated generator identity.

This is derived internal content. The proof uses the published transpose
formulas in `UnitCocycleDescent.Effective`, Mathlib's
`StructureSheaf.toOpen_comp_comap`, and the restriction identity
`tilde.toOpen_res`. It introduces no new descent, gluing or
representability premise.
