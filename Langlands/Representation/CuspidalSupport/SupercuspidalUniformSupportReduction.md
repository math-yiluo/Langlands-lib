# Renard VI.2.4 from four Chapter V structural statements

This module proves that Proposition VI.2.4 of Renard,
`SupercuspidalUniformCoefficientSupportStatement.{u, v}`, follows from four
published structural propositions, taken as explicit premises. The result is a
conditional, intermediate reduction.

Three of the four premises already have unconditional Library proofs:

- `GroupScheme.parabolicDynamic : ParabolicDynamicStatement.{u}`
  (`Langlands/GroupScheme/Absolute/ParabolicDynamicProof.lean`);
- `GroupScheme.standardCocharacter : StandardCocharacterStatement.{u}`
  (`Langlands/GroupScheme/Rational/StandardCocharacterProof.lean`);
- `GroupScheme.relativeRootSystem : RelativeRootSystemStatement.{u}`
  (`Langlands/GroupScheme/Rational/RelativeRootSystemProof.lean`).

The one outstanding obligation is the fourth premise,
`BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`,
which has no Library proof yet. This module therefore does not prove VI.2.4
unconditionally, nor the aggregate target `UniformAdmissibilityStatements`.
The three proved premises are kept as hypotheses only so that the statement
mirrors the Library theorems it uses. Supplying `parabolicDynamic`,
`standardCocharacter` and `relativeRootSystem` turns it into the implication
from `JointSpecialCompactBasisExistenceStatement` alone.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Proposition VI.2.4 (printed pp.141–142 /
PDF pp.147–148). It is registered as
`renard-2026-representations-groupes-reductifs-padiques`. The conclusion is
the published proposition in
`Langlands/Representation/CuspidalSupport/UniformAdmissibilityStatements.lean`,
whose Markdown gives its correspondence with the source.

## The reduction statement

`SupercuspidalUniformCoefficientSupportReductionStatement.{u, v}` is the
implication

```
GroupScheme.ParabolicDynamicStatement.{u} →
  GroupScheme.StandardCocharacterStatement.{u} →
    GroupScheme.RelativeRootSystemStatement.{u} →
      BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
        SupercuspidalUniformCoefficientSupportStatement.{u, v}
```

Here `u` is the universe of the local field and `v` that of the representation
carriers. The premises, all published Library propositions, are:

- `ParabolicDynamicStatement`: the parabolic subgroups of a connected reductive
  group are exactly the dynamic subgroups `P(χ)` (Milne, Theorem 25.1);
- `StandardCocharacterStatement`: standard cocharacters exist, and each
  standard parabolic, Levi and unipotent subgroup is the corresponding dynamic
  subgroup of every standard cocharacter;
- `RelativeRootSystemStatement`: the relative roots of a maximal split torus form
  a root system (Milne 25.16–25.17);
- `JointSpecialCompactBasisExistenceStatement`: at one special vertex, a common
  witness for the special compact subgroup, the Iwasawa and Cartan
  decompositions and a simultaneous compact-open basis (Renard, Chapter V).

The conclusion is VI.2.4 exactly as published: for every compact open subgroup
`K` of `G(F)` there is an open set `Ω`, contained in `C · Z(G)` for a compact
`C`, such that for every irreducible supercuspidal smooth complex
representation `A`, every `K`-fixed vector `w` and every `K`-invariant linear
form `ℓ`, the support of `g ↦ ℓ(A(g) w)` lies in `Ω`. Nothing else is assumed.

These four premises are exactly those of the two Library theorems used below:
`RepresentedParabolic.compactRestriction_of_isSupercuspidal` (all four) and
`rationalNormKernelUniformSupport_of_joint` with the relative root system and
standard cocharacters (the last three).

The statement is internal content. It is an implication between published
Library propositions, and the same module proves it.

## Generic lemmas

These are in namespace `Langlands.CompactCoefficientClass` and concern an
arbitrary topological group.

- `exists_isCompact_openSubgroup_le`: if one open subgroup `L₀` is compact,
  every open subgroup `U` contains the compact open subgroup `U ∩ L₀`.
- `support_subset_of_iSup_eq_top`: let `A` be a smooth complex representation
  with compact smooth-dual coefficients. Assume `A` is the span of a family of
  irreducible subrepresentations `W i`, and every open subgroup contains a
  compact open one. Let `K` be a compact open subgroup and `C` a set containing
  the support of every inverse coefficient `h ↦ ℓ(D(h⁻¹) v)` of every irreducible
  compact representation `D`, with `v` in `D^K` and `ℓ` a `K`-invariant linear
  form. Then `C` also contains the support of `h ↦ ℓ(A(h⁻¹) w)` for every `w`
  in `A^K` and every `K`-invariant `ℓ`.
- `exists_conj_level`: for a compact open subgroup `K` and an element `r`, the
  compact open subgroup `L = K ∩ r⁻¹Kr` satisfies `L ≤ K` and `rLr⁻¹ ⊆ K`.
- `isCompact_comap_subtype`: a compact open subgroup contained in a subgroup
  `H` stays compact when pulled back to `H`.

The proof of `support_subset_of_iSup_eq_top` uses the `K`-averaging operator
`Compact.CharZero.averageMap`. It fixes `w`, so it is enough to bound the
coefficients of `avg x` for every `x`. These are additive in `x`, so by
`Submodule.iSup_induction` it is enough to take `x` in one `W i`. Averaging
commutes with the inclusion of `W i`, so `avg x` is a `K`-fixed vector of the
subrepresentation `W i`. That subrepresentation is irreducible and has compact
smooth-dual coefficients (`hasCompactSmoothDualCoefficients_subrepresentation`),
so it is an object of `IrreducibleCompactCoefficientRep`. The form `ℓ` restricted
to `W i` is still `K`-invariant, so the hypothesis on `C` applies.

## Proof

`supercuspidalUniformCoefficientSupportReduction` proves the reduction
statement. Write `H = ⁰G` for `Plancherel.rationalCommonNormKernel G` and `Z`
for the centre of `G(F)`.

1. **Choices that do not depend on the representation.** The compact subgroup
   `K` lies in `H` (`Plancherel.compactSubgroup_le_rationalCommonNormKernel`).
   The subgroup `H ⊔ Z` has finite index
   (`rationalCommonNormKernel_sup_center_finiteIndex`). For each coset `q` in
   the finite quotient `Q = G(F)/(H ⊔ Z)` take the representative `r_q`, its
   chosen `out`. Let `L_q = K ∩ r_q⁻¹ K r_q` (`exists_conj_level`), and `L_q^H`
   its pullback to `H`, a compact open subgroup of `H`. A maximal split torus
   with a generic cocharacter exists
   (`exists_maximalSplitTorus_genericCocharacter`). With the relative root system
   at that torus and the closedness of the standard unipotent subgroups
   (`isClosed_unipotent_of_isNonarchimedeanLocalField`),
   `rationalNormKernelUniformSupport_of_joint` gives, for each `q`, a compact set
   `C_q ⊆ H`. It contains the inverse coefficients at level `L_q^H` of all
   irreducible compact representations of `H`.
2. **The set `Ω`.** Let `S = ⋃_q { r_q h⁻¹ | h ∈ C_q }`. It is compact as a
   finite union of continuous images of compact sets. Put `Ω = S · K · Z`. It
   is open because `K` is open, and it equals `(S · K) · Z` with `S · K`
   compact.
3. **Reduction to `⁰G`.** Let `A` be irreducible and supercuspidal, `w ∈ A^K`,
   `ℓ` a `K`-invariant form, and `ℓ(A(g) w) ≠ 0`. Write `g = r_q a z` with
   `a ∈ H` and `z ∈ Z`. This uses `QuotientGroup.mk_out_eq_mul` and
   `H ⊔ Z = H · Z` (`Subgroup.mul_normal`). Then `ℓ(A(g) w) = ℓ'(A(a) w')`
   with `w' = A(z) w` and `ℓ' = ℓ ∘ A(r_q)`. The vector `w'` is `K`-fixed
   because `z` is central. The form `ℓ'` is `L_q`-invariant because
   `r_q L_q r_q⁻¹ ⊆ K`.
4. **The restriction to `⁰G`.** The restriction of `A` to `H` has compact
   smooth-dual coefficients (VI.2.1, (a) ⇒ (c):
   `RepresentedParabolic.compactRestriction_of_isSupercuspidal`). It is spanned
   by finitely many irreducible subrepresentations (VI.3.2(ii):
   `rationalNormKernelFiniteRestriction`). Since `K` pulled back to `H` is a
   compact open subgroup, `exists_isCompact_openSubgroup_le` applies.
   `support_subset_of_iSup_eq_top` at level `L_q^H` then gives `a⁻¹ ∈ C_q`.
   Hence `r_q a ∈ S` and `g = (r_q a) · 1 · z ∈ Ω`.

## Comparison with the source

Renard's proof of VI.2.4 uses the uniform admissibility theorem VI.2.3. It
bounds the powers of positive elements of the Cartan monoid that can occur in
the support by `N = c(G, K)` and then applies the Hecke decomposition of
Remark V.5.3. The Lean proof takes a different route and does not use VI.2.3.
It applies the Library's uniform support for the compact coefficients of `⁰G`.
That result, proved from the joint special-compact data, a compression level
and a central Cartan cover, is the support obligation of VI.3.4. The Lean proof
combines it with VI.2.1 (a) ⇒ (c), the semisimple restriction of VI.3.2(ii), and
the finiteness of `G(F)/⁰G Z(G)`. These Library results are proved
independently of VI.2.4, so the route is not circular. The conclusion is
unchanged; only the proof differs.
