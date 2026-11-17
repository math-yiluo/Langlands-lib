# Cartan components and simple-root support in adjoint root data

This module is the adjoint counterpart of
`Langlands.LinearAlgebra.SimplyConnectedCartanComponents`. That module uses simple-coroot
coordinates when the coroots span the coweight lattice. This one uses simple-root coordinates
when the roots span the weight lattice. It reuses the Cartan components from that module
unchanged: `cartanSetoid b`, `Component b` and `component b`, defined for any base `b` of a root
datum `P : RootDatum J X Y`. Two simple indices are in the same component when they are joined
by a chain of nonzero Cartan pairings.

## Content

Assume `hspan : P.rootSpan ℤ = ⊤`.

- `simpleRootBasis b hspan : Basis b.support ℤ X` is the basis of simple roots. The simple roots
  are linearly independent (`RootPairing.Base.linearIndepOn_root`), and they span the integral
  root span (`RootPairing.Base.span_int_root_support`), which is everything by `hspan`.
  `simpleRootBasis_apply` identifies its vectors with the simple roots.
- `simpleRootCoordinates b hspan : X ≃ₗ[ℤ] (b.support → ℤ)` takes a weight to its simple-root
  coefficients (`Basis.equivFun`). `simpleRootCoordinates_root_self` and
  `simpleRootCoordinates_root_of_ne` compute the coordinates of a simple root.
- `RootSupported b hspan c x` says that the simple-root coefficients of `x` vanish at every simple
  index outside the component `c`. A simple root is supported on its own component
  (`rootSupported_simple`). Supported weights are closed under negation, subtraction and integral
  multiples. A supported weight pairs to zero with every simple coroot outside `c`
  (`RootSupported.pairing_eq_zero`), because simple roots and simple coroots in different
  components have zero Cartan pairing. A nonzero weight is supported on at most one component
  (`RootSupported.component_eq`).
- For a finite reduced root datum, `exists_rootSupported` proves that every root is supported on
  some component. The proof is Mathlib's induction `RootPairing.Base.induction_reflect` over
  simple reflections. The property holds for simple roots and is preserved by `r ↦ -r`. Reflection
  in a simple root `α_j` sends `α` to `α - ⟨α, α_j^∨⟩ α_j`. If `j` is in the component `c` of `α`,
  the result is still supported on `c`. Otherwise `⟨α, α_j^∨⟩ = 0` by the pairing lemma and the
  root is unchanged.
- `existsUnique_rootSupported` adds uniqueness (roots are nonzero). `rootComponent b hspan r` is
  that unique component, `rootSupported_rootComponent` and
  `simpleRootCoordinates_root_eq_zero` record that the coefficients of a root vanish outside its
  component, and `rootComponent_simple` shows that a simple root's component is the component of
  its index.

## Provenance

This is internal linear algebra. Conrad, *Reductive group schemes* (2014), Remark 6.4.5, says
that Proposition 6.4.4 holds for adjoint groups because "an 'adjoint' root datum is a direct
product of irreducible ones, as in the simply connected case". The simple-root coordinates and
the component of each root are the integral form of that decomposition of the weight lattice.
That every root is an integral combination of simple roots from one connected component of the
Dynkin diagram is standard (for example Bourbaki, *Lie groups and Lie algebras*, Ch. VI §1.2).
Here it is proved directly from Mathlib's base API.
