# Determinant twists of presented local components for any Hecke character

Author: Worker 5136.

A finite tensor presentation `P` of a nonzero finite realization `S` has, at each
finite place `v`, a local component `P.localComponent hS v`: a local realization
inside the forms of `S`, equivalent to the local factor `ρ v` (the Library's
`PresentedLocalComponent`). For an arbitrary Hecke character `χ`, this internal
module multiplies that component by `χ ∘ det`.

- A private lemma `scalarCovariance_exists_fixed`: a scalar-covariant linear
  equivalence carries a nonzero vector fixed by a subset `K` to a nonzero fixed
  vector, provided the scalar character is `1` on `K`.
- `FiniteTensorPresentation.heckeDeterminantTwistLocalComponent P hS χ v`: the
  twist `LocalRealization.heckeDeterminantTwist` (module `FiniteLocalTwist`) of
  the local component. It is nonzero (`_ne_bot`) and lies in the local
  restriction of `S.heckeDeterminantTwist χ` (`_le`).
- `heckeDeterminantTwistLocalComponentEquiv`: the local factor `ρ v` twisted by
  `χ_v ∘ det` is equivalent to the representation on this twisted component.
  The `_apply` and `evaluate_` lemmas describe it on vectors.
- `heckeDeterminantTwistLocalFactor_isSmooth`: `(χ_v ∘ det) ⊗ ρ v` is smooth,
  since it embeds in the smooth twisted component.
- `heckeDeterminantTwistLocalComponentClass` and `_eq`: the isomorphism class of
  the twisted component depends only on the local tensor data, not on the
  finite realization.
- `heckeDeterminantTwistLocalComponent_exists_integral_fixed`: if `v ∉ E` and
  `χ_v ∘ det` is trivial on `GL_n(𝒪_v)`, the twisted component has a nonzero
  `GL_n(𝒪_v)`-fixed vector.

Provenance: internal. This is the Library module
`Langlands.Automorphic.PresentedComponentDeterminantTwist` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.
