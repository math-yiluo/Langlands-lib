# Modular character of actual infinite adelic points

For any number field `F : Type u` and affine group scheme `G` over `F`
whose structure morphism is locally of finite type,
`InfiniteAdelicGroupPoints.modularCharacter_eq_prod` computes the intrinsic
modular character of the existing infinite adelic point group:

\[
\Delta_{G(F_\infty)}(g)
  =\prod_{w\mid\infty}\Delta_{G(F_w)}(g_w).
\]

The infinite adelic point group is the actual group of points over
`InfiniteAdeleRing F`. Each factor is the actual completion-valued point
group `InfinitePlaceGroupPoints F G w`, and `g_w` is the existing
`InfiniteAdelicGroupPoints.atPlace F G w g`. All groups retain their
regular-function evaluation topologies. The number field has arbitrary
universe `u`. The result requires no smoothness, connectedness,
reductivity, splitting, positive dimension, or local modular comparison.

The proof applies existing continuous multiplicative equivalence
transport to `InfiniteAdelicGroupPoints.completions F G`, then uses the
proved generic finite dependent product formula
`Langlands.ProductMeasure.modularCharacter_pi`. The local point groups
are locally compact Hausdorff topological groups by the existing
finite-coordinate point construction and local compactness of each
completion. The module exposes these existing topological group, Hausdorff
and locally compact properties through instances for the local point alias.
Finiteness of the infinite places follows from the number field hypothesis. The completion equivalence and the coordinate
projections are the existing ones; no substitute point carrier or
topology is introduced.

`localModularProduct F G` is the displayed local product as a monoid
homomorphism on the original infinite adelic point group.
`localModularProduct_apply` identifies it pointwise with that group's
intrinsic modular character. Its homomorphism laws follow from the
projection homomorphisms, the local modular homomorphisms and finite
product multiplicativity.

The module equips the infinite adelic point group with the Borel sigma
algebra of its existing topology. In the convention of positive right
pushforward, `map_mul_right_haar_eq_prod` states

\[
(R_g)_*\operatorname{haar}_{G(F_\infty)}
 =\left(\prod_{w\mid\infty}\Delta_{G(F_w)}(g_w)\right)
   \operatorname{haar}_{G(F_\infty)},\qquad R_g(x)=xg.
\]

This is the fixed Mathlib left Haar measure on that same actual point
group. The proof rewrites the existing regular-Haar scaling formula by
the product identity; it does not select or construct a product measure.

The provenance is internal: this is a direct specialization of existing
actual point-product and modular-character theorems. It supplies the
archimedean product step in the adelic comparison motivated by
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Section 3.6, equations (3.12)–(3.13), printed pages 89–90. The five-page
October 2026 author errata contain no correction to Section 3.6.

The generic product modular-character module is a separately submitted
prerequisite and must be integrated first. This unit does not prove
the local determinant/Jacobian comparison, the finite-adelic product
formula, the full adelic character-norm comparison, reductive determinant
triviality, or `AdelicHaarUnimodularityStatement`.
