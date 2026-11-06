# Connectedness of subgroups containing a Borel, from conjugacy and the normalizer theorem

Worker 1427. The module uses the published helper
[BorelContainingFactor](BorelContainingFactor.md) by Worker 1368 and the
published [identity component](../IdentityComponent.md).

This module proves `BorelContainingSubgroupConnectedStatement.{u}` from two
explicit hypotheses: `BorelConjugacyStatement.{u}` and
`BorelNormalizerStatement.{u}`. Both are published statements from
[BorelStatement](BorelStatement.md). Neither is proved here. The target, the
two hypotheses and all imported modules are unchanged.

## Conjugation on points

`BorelContainingSubgroupConnected.mul_mul_inv_eq_comp_innerIso`: let `G` be a
group scheme over any base scheme `S`, and let `g` and `h` be sections of `G`
over `S`. Then `g * h * g⁻¹` is `h` composed with the inner automorphism
`G.innerIso g`. This holds because composing a section with the inner
automorphism is conjugation by the corresponding constant point
(`comp_innerIso_hom`, `constantPoint_self`). The lemma is used to rewrite
membership in an abstract normalizer of `G(k)`.

## Points of `P` lie in the identity component

In this section `k : Type u` is algebraically closed. `G` is smooth, affine and
has connected underlying space. `P` is smooth and affine. The final reduction
below derives affineness of `P` from its closed embedding into `G`, so it adds
no affineness assumption on `P`.

`BorelContainingSubgroupConnected.exists_comp_identityComponentι_eq`: assume
`BorelConjugacyStatement.{u}` and `BorelNormalizerStatement.{u}`. Let
`i : P ⟶ G` be a closed subgroup, `j : B ⟶ G` a Borel subgroup and
`f : B ⟶ P` a map with `f ≫ i = j`. Then every `k`-point `x` of `P` factors
through the identity component `identityComponentι P : P⁰ ⟶ P`.

The proof follows Milne's proof of Corollary 17.49, applied to `x ∈ P(k)`
instead of a point of the normalizer of `P`.

1. Since `B` is connected, `f` factors as `f₀ : B ⟶ P⁰`
   (`IdentityComponent.factor`). The composite `P⁰ ⟶ P ⟶ G` is a closed
   subgroup, so `IsBorelSubgroup.of_comp` makes `f₀` a Borel subgroup of `P⁰`.
2. The conjugate `f ≫ int(x)` also factors through `P⁰`, as `fx`. Its
   composite into `G` is `j ≫ int(x')`, where `x'` is the image of `x` in
   `G(k)` (`innerIso_hom_comp`). This is Borel by `IsBorelSubgroup.comp_iso`,
   so `fx` is a Borel subgroup of `P⁰`.
3. `P⁰` is smooth, affine and connected over `k`. The conjugacy component of
   `BorelConjugacyStatement` gives a point `p ∈ P⁰(k)` and an isomorphism
   `φ : B ≅ B` with `f₀ ≫ int(p) = φ.hom ≫ fx`. Let `q` be the image of `p`
   in `G(k)`. Then `j ≫ int(q) = φ.hom ≫ j ≫ int(x')`.
4. Put `w = x'⁻¹ * q`. By `innerIso_mul_hom` and `innerIso_inv_hom`,
   `j ≫ int(w) = φ.hom ≫ j`, and also `j ≫ int(w)⁻¹ = φ.inv ≫ j`. Using the
   lemma of the previous section, these two equations show that `w` is in the
   abstract normalizer in `G(k)` of the image of `B(k)`.
5. `BorelNormalizerStatement` rewrites that normalizer as the image of
   `B(k)`. So `w` is the image of some `b ∈ B(k)`.
6. The point `y = p * (f₀(b))⁻¹` of `P⁰` maps to `x`. Since `i` is a
   monomorphism, this is checked after composing with `i`, where it reads
   `q * w⁻¹ = x'`. That identity follows from `w = x'⁻¹ * q`.

## The reduction

`BorelContainingSubgroupConnected.borelContainingSubgroupConnected_of`:
`BorelConjugacyStatement.{u}` and `BorelNormalizerStatement.{u}` together imply
`BorelContainingSubgroupConnectedStatement.{u}`.

Fix the data of the target: `k`, `G`, the smooth closed subgroup `i : P ⟶ G`,
the Borel subgroup `j : B ⟶ G` and `f` with `f ≫ i = j`. `P` is affine because
its closed immersion into affine `G` is affine (`isAffineHom_source`). It is
locally of finite type over `k` because it is smooth, so its underlying space
is a Jacobson space.

It suffices to show that the connected component of the identity point of `P`
is the whole space. This component is the published `identitySet P`, which is
clopen. Suppose its complement is nonempty. The complement is open, hence
locally closed, so it contains a closed point `a` of `P`
(`nonempty_inter_closedPoints`). Because `k` is algebraically closed and `P`
is locally of finite type, `a` is the image of a `k`-point `x` of `P`
(Mathlib's `pointOfClosedPoint`). By the previous
section `x` factors through `P⁰`. The range of `identityComponentι P` is
`identitySet P` (`IdentityComponent.range_identityComponentι`), so `a` lies in
`identitySet P`. This contradicts the choice of `a`.

## Literature

The route is Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Corollary 17.49 and its proof, printed p.367
(one-based PDF p.383). Milne takes `x ∈ N_G(P)(k)` and a Borel subgroup
`B ⊂ P`. Then `B` and `xBx⁻¹` are Borel subgroups of `P⁰`, so
`B = (px)B(px)⁻¹` for some `p ∈ P⁰(k)` (17.10). By the normalizer theorem
(17.48), `px ∈ B(k)`, so `x ∈ P⁰(k)`.

This module needs only connectedness. It applies the argument only to
`x ∈ P(k)`, which lies in `N_G(P)(k)`. Milne also proves smoothness of
`N_G(P)` (Lemma 17.47) for the self-normalization clause. That step is not used
here, since `P` is smooth by hypothesis. Milne passes from `P⁰(k) = P(k)` to
`P = P⁰` through smoothness. Here that step is the topological Jacobson
argument above. The roles of `B` and `xBx⁻¹` in Milne's conjugation are
expressed by the actual embeddings `f₀` and `fx` and the isomorphism `φ`.

This module keeps both statements as hypotheses. The unconditional theorem,
which supplies their published proofs, is in
[BorelContainingSubgroupConnected](BorelContainingSubgroupConnected.md).
