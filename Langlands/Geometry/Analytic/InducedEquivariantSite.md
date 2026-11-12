# Induction on `G`-spaces and on equivariant quasi-étale sites

Author: Worker 21.

This module defines the functors through which Berkovich's Example 1.2.1(i)
compares the quasi-étale site of an `H`-space `X` with that of its induced
`G`-space `X_{G/H}`. The induced objects must be `G`-spaces, and the induced
morphisms must be quasi-étale. These facts are the statements
`InducedSpace.ContinuityStatement` (module `InducedSpaceContinuityStatement`)
and `InducedSpace.MorphismPropertyStatement` (module
`InducedQuasiEtaleStatement`), which are not yet proved. The functors here
take proofs of them as explicit arguments `hC` and `hQ`. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

## Declarations

Let `G : Type z` be a topological group, `H` a subgroup with
`hH : IsOpen (H : Set G)`, and `hC : ContinuityStatement.{u, v, z}`.

- `gSpaceInduction hH hC : GSpace K H ⥤ GSpace K G` is the induction functor
  `inductionFunctor H` (module `InducedSpaceAdjunction`), lifted to the full
  subcategories of `G`-spaces (Mathlib's `ObjectProperty.lift`). The lift
  uses `hC` to show that `X_{G/H}` is a `G`-space.
  `gSpaceInduction_obj_obj` records that the underlying object is
  `inducedAction H X.obj`.
- With `hQ : MorphismPropertyStatement.{u, v, z}` and an `H`-space `X`:
  `quasiEtaleSiteInduction hH hC hQ X : EquivariantQuasiEtaleSite X ⥤
  EquivariantQuasiEtaleSite ((gSpaceInduction hH hC).obj X)`. It sends an
  object `U(H) → X(H)` of Berkovich's `Qét(X(H))` (module
  `EquivariantQuasiEtaleSite`) to `U_{G/H}(G) → X_{G/H}(G)`, and a morphism
  over `X` to its induction. The structure morphism is quasi-étale by `hQ`.
  `quasiEtaleSiteInduction_obj_left` and `quasiEtaleSiteInduction_map_left`
  record the values.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, Example 1.2.1(i), printed p.3: "Let N be an open subgroup of a
topological group G, and let X be an N-space. Then the morphism
X(N) → X_{G/N}(G) induces an isomorphism of sites X(N)_qét ⥲ X_{G/N}(G)_qét
(resp. X(N)_ét ⥲ X_{G/N}(G)_ét) and, therefore, an isomorphism of the
corresponding topoi."

## Derived choices

- Berkovich's morphism of sites is given by the pullback functor
  `V(G) ↦ (X ×_{X_{G/N}} V)(N)` along the unit `X → X_{G/N}`. Here the
  comparison is the induction functor `U(N) ↦ U_{G/N}(G)` in the other
  direction, its expected inverse. Berkovich's proof of Theorem 1.4.2
  (printed pp.8–9) works with these induced objects: "We claim that the
  family of objects {U_{G/N}(G)} is cofinal in the category C(U/X(G))". This
  direction needs no fibre products of `G`-spaces.
- The two unproved facts enter as hypotheses `hC` and `hQ`, not as
  assumptions about the output objects. The equivalence and the comparison
  of coverings are the statement `QuasiEtaleSiteEquivalenceStatement`
  (module `InducedSiteEquivalenceStatement`).
- Only the quasi-étale site is treated. The étale case is analogous, using
  the étale part of `MorphismPropertyStatement`.
