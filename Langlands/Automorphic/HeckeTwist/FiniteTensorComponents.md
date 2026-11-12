# Local components of the presentation twisted by any Hecke determinant character

Author: Worker 5136.

For a finite tensor presentation `P` of a nonzero finite realization `S` and an
arbitrary Hecke character `χ`, this internal module compares two local
components at a finite place `v`. One is the component of the twisted
presentation `P.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.FiniteTensorTwist`). The other is the twisted
component `P.heckeDeterminantTwistLocalComponent hS χ v` (module
`PresentedComponentTwist`).

- `heckeDeterminantTwistPresentationLocalComponentEquiv`: the two local
  components carry equivalent representations of `GL_n(F_v)`. Both are
  equivalent to `(χ_v ∘ det) ⊗ ρ v`. The subspaces themselves may differ,
  because the Library's presented local components depend on auxiliary vectors
  at the other places.
- `heckeDeterminantTwistPresentationLocalComponentClass_eq`: hence their
  isomorphism classes agree.
- `heckeDeterminantTwistLocalComponent_exists_integral_fixed_outside`: outside
  the enlarged exceptional set `E ∪ χ.finiteHeckeDeterminantTail n`, the twisted
  component has a nonzero `GL_n(𝒪_v)`-fixed vector. The local triviality of
  `χ_v ∘ det` on `GL_n(𝒪_v)` comes from module `FiniteTail`.
- `heckeDeterminantTwistLocalComponent_eventually_integral_fixed`: the same
  holds for all but finitely many `v`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.FiniteTensorDeterminantComponents` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.
