# A `G`-space over an induced space is induced from the domain over the base copy

Author: Worker 933.

This module proves that a `G`-object `Y` with a `G`-morphism `π : Y → X_{G/H}`
is induced from the domain `π⁻¹(X_H)` of `Y` that lies over the copy of `X`
indexed by the coset `H`. The proof assumes the statement
`OpenPartitionCoproductStatement` as a hypothesis. It is the main step of
essential surjectivity in Berkovich's Example 1.2.1(i), and a helper for the
proof of `InducedSpace.QuasiEtaleSiteEquivalenceStatement` (module
`InducedSiteEquivalenceStatement`). Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

## Setting

Let `G : Type z` be a group and `H` a subgroup. Let `X` be an `H`-object and `Y`
a `G`-object of `LocalizedCategory` (Lean types
`Action (LocalizedCategory …) H` and `Action (LocalizedCategory …) G`). Let
`π : Y ⟶ inducedAction H X` be a `G`-morphism to the induced space `X_{G/H}`
(module `InducedAnalyticSpace`). The following come from module
`InducedSiteBase`:

- `preimageDomain π c` is the open domain `π⁻¹(X_c)` of `Y`, where `X_c` is the
  copy of `X` indexed by the coset `c`.
- `baseAction π` is the `H`-object `π⁻¹(X_H)`: the domain
  `preimageDomain π (baseCoset H)` with the restricted action of `H`.
- `baseInclusion π : baseAction π ⟶ Y` is its inclusion, a morphism of
  `H`-objects (with `Y` restricted to `H`).

`lift H φ` (module `InducedAnalyticSpace`) is the `G`-morphism
`Z_{G/H} → Y` that extends an `H`-morphism `φ : Z → Y`. On the copy indexed by
`c` it is `φ` followed by the action of the representative `c.out`
(`copy_liftHom`).

## Declarations

- `preimageDomainIso π c : (baseAction π).V ≅ domainObj Y.V (preimageDomain π c)`.
  This is the restriction of the action `Y.ρ c.out` to an isomorphism from
  `π⁻¹(X_H)` onto `π⁻¹(X_c)`. Its inverse is the restriction of
  `Y.ρ c.out⁻¹`.
- `copy_lift_baseInclusion_hom π c`: on the copy indexed by `c`, the morphism
  `(lift H (baseInclusion π)).hom` equals
  `(preimageDomainIso π c).hom ≫ domainι Y.V (preimageDomain π c)`.

The remaining statements take a hypothesis
`hP : OpenPartitionCoproductStatement.{u, v, z}` (module
`OpenPartitionCoproductStatement`). This statement says: an analytic space whose
underlying space is the disjoint union of open subsets `U_j` is the coproduct of
the open domains `U_j`. The results hold for every such `hP`. The statement
itself is not proved here.

- `nonempty_isColimit_preimageDomain π hP`: the canonical morphisms
  `domainι Y.V (preimageDomain π c)`, for `c ∈ G ⧸ H`, make `Y.V` a coproduct.
- `isIso_lift_baseInclusion_hom π hP`: the underlying morphism
  `(lift H (baseInclusion π)).hom` is an isomorphism.
- `isIso_lift_baseInclusion π hP`: `lift H (baseInclusion π)` is an
  isomorphism of `G`-objects `(π⁻¹(X_H))_{G/H} ≅ Y`.

## Proof

`preimageDomainIso`. The action of `g ∈ G` maps `π⁻¹(X_c)` into `π⁻¹(X_{g c})`
(`ρ_mem_preimageDomain`). Since `c.out • H = c` (`out_smul_baseCoset`) and
`c.out⁻¹ • c = H` (`out_inv_smul`), the isomorphism `Y.ρ c.out` of `Y.V`
(Mathlib's `Action.ρAut`) maps `π⁻¹(X_H)` into `π⁻¹(X_c)`, and its inverse maps
`π⁻¹(X_c)` into `π⁻¹(X_H)`. Library `domainRestrictIso` (module
`QuasiEtaleDomains`) restricts it to an isomorphism of the domains.

`copy_lift_baseInclusion_hom`. The copy `c` followed by the extension is
`ν_H ≫ Y.ρ c.out` by `copy_liftHom`, where `ν_H` is the inclusion of
`π⁻¹(X_H)`. By `domainRestrictIso_hom_inclusion` this equals
`(preimageDomainIso π c).hom ≫ ν_c`, where `ν_c` is the inclusion of
`π⁻¹(X_c)`.

`nonempty_isColimit_preimageDomain`. Apply `hP` to the open sets `π⁻¹(X_c)`.
A point `y` of `Y` lies in `π⁻¹(X_c)` exactly when the coset of `π(y)` is `c`
(`mem_preimageDomain_iff`). So these sets are pairwise disjoint, and `y` lies in
`π⁻¹(X_c)` for `c` the coset of `π(y)`.

`isIso_lift_baseInclusion_hom`. Write `L` for the extension and `e_c` for
`preimageDomainIso π c`. Both `X'_{G/H}` (with `X' = π⁻¹(X_H)`) and `Y.V` are
coproducts over `G ⧸ H`: the first of the copies (`copies_hom_ext`), the second
of the domains `π⁻¹(X_c)` (previous lemma). Let `M : Y.V → X'_{G/H}` be the
morphism that is `e_c⁻¹ ≫ copy c` on the domain `π⁻¹(X_c)`. On the copy `c`,
`L ≫ M` is `e_c ≫ ν_c ≫ M = e_c ≫ e_c⁻¹ ≫ copy c = copy c`. On the domain
`π⁻¹(X_c)`, `M ≫ L` is `e_c⁻¹ ≫ copy c ≫ L = e_c⁻¹ ≫ e_c ≫ ν_c = ν_c`. So `M` is
an inverse of `L`.

`isIso_lift_baseInclusion`. A morphism of actions whose underlying morphism is an
isomorphism is an isomorphism (Mathlib's `Action.isIso_of_hom_isIso`).

## Original source and provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
§1.1.2 (printed p.2) builds `X_{G/H}` as the disjoint union of copies of `X`
indexed by `G/H`. §1.2, Example 1.2.1(i) (printed p.3) states without proof that
induction gives an isomorphism of sites. This module proves one step of that
statement, essential surjectivity: a `G`-space over `X_{G/H}` is the induction of
its part over the copy `X_H`. The argument is derived for this formalization and
is not in the source. The coproduct property of an open partition is the separate
statement `OpenPartitionCoproductStatement`, taken here as a hypothesis.
