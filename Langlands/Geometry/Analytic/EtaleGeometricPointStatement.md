# Geometric points are points of the étale site

Author: Worker 21.

This module states, without proof, that geometric points of an analytic space
give points of its étale site. It contains one Prop-valued definition,
`Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite.GeometricPointStatement`.

## Statement

For every ground field `K` (a complete ultrametric normed field, the valuation
possibly trivial), every normed field `L` over `K` (`[NormedAlgebra K L]`) that
is ultrametric, complete and algebraically closed, every analytic space
`X : LocalizedCategory.{u, v, v} (K := K)` and every `L`-valued point
`x : (localizedFieldPointFunctor L).obj X` (module `FieldValuedPoints`), the
fibre functor `pointFibre L x` on `Ét(X)` satisfies `PointAxioms L x` (module
`EtaleGeometricPoints`):

1. its category of elements is cofiltered;
2. for every covering sieve `R` of an object `U` of `Ét(X)` for
   `etaleTopology X`, and every `L`-valued point `p` of `U` over `x`, there are
   a morphism `f : V ⟶ U` in `R` and an `L`-valued point `q` of `V` over `x`
   with `f` sending `q` to `p`.

With a proof `h`, `toPoint L x (h K L X x)` is a point of the étale site in
Mathlib's sense, and `pointEquivariance` makes such points compatible with a
group action.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, §4.2,
printed p.87 / PDF p.84:

- stalks: "The inverse image of a sheaf F with respect to i_x is denoted by F_x
  and is called the stalk of F at x. (We identify F_x with the corresponding
  discrete G_ℋ(x)-set.)";
- proof of Proposition 4.2.2: "The set F_x(ℋ(x)) is the inductive limit of the
  sets F(Y, T) over all ((Y, T) → (X, S)) ∈ Ét(X, S) with a fixed point y ∈ T
  over x such that ℋ(x) ⥲ ℋ(y).";
- Corollary 4.2.3: "A morphism of sheaves F → G on (X, S) is a mono
  [epi/isomorphism] if and only if for all x ∈ X the induced maps F_x → G_x
  possess the same properties."

Berkovich works with the stalk at `x` as a discrete Galois set, that is, with
the stalks at the geometric points over `x`. He does not formulate fibre
functors. The formulation as Mathlib's site points (the fibre functors of
SGA 4 IV 6.3, Mathlib `GrothendieckTopology.Point`) with `L`-valued points for
an arbitrary complete algebraically closed `L` is derived. Its expected proof
uses:

- for (1), fibre products in `Ét(X)` and the fact that the diagonal of an étale
  morphism is an open immersion;
- for (2), that the residue field extensions of étale morphisms are finite
  separable (Berkovich 1993 §3.4), so that embeddings into the algebraically
  closed `L` extend, and that completed residue fields do not depend on the
  chart.
