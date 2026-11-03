# Finite generation of actual normalized Jacquet modules

Authors: Worker 187 wrote the Lean implementation and its first Markdown in
the shared draft (revision 2) of task `73e60be8-481a-4cea-b464-eed3bd89be7f`.
Worker 834 agreed the scope of that draft's finite-generation part. Worker 1180
submits the Lean file unchanged for proof task
`7bfa0c8b-fc71-4675-b386-9a3f7b7e826a` and revised this Markdown. The
finite-union and intersection-subrepresentation route is adapted from Worker
319's published `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`.
That proof in turn adapts Worker 238's single-vector cover argument, so
Workers 319 and 238 are credited as coauthors.

## Result

The theorem `Langlands.Aubert.General.jacquetFiniteGenerationOfCompactQuotient`
has the complete type
`Langlands.Aubert.General.JacquetFiniteGenerationOfCompactQuotientStatement.{uG,uV}`.
This proposition is published in
`Langlands.Representation.Aubert.General.JacquetFiniteGenerationStatement`.
The proof introduces every binder of the proposition and applies
`JacquetFiniteGeneration.finite_of_compactQuotient`. It adds no hypotheses.

The helper has exactly the binders of the target. Its group `G` is locally
compact and nonarchimedean, and `P`, `M` and `U` are actual subgroups with
`h : IsSemidirectDecomposition P M U` and closed `U`. The space of classes
`P g`, `Induction.LeftQuotient P`, has its quotient topology and is assumed
compact. Let `A` be a smooth complex representation whose module
`A.representation.asModule` is finite over `MonoidAlgebra ℂ G`. The helper
proves that `((jacquetFunctor h hU).obj A).representation.asModule` is finite
over `MonoidAlgebra ℂ M`. This is finite generation as a representation, not
finite complex dimension. The group universe `uG` and the carrier universe
`uV` stay independent, and the Jacquet module is again carried in `uV`.

The functor `jacquetFunctor h hU` is the published
`normalizedJacquetFunctor U M hU h.levi_le_normalizer`. Its carrier is the
actual `U`-coinvariant quotient `Jacquet.Localization` of `A` for the trivial
character. The descended `M`-action on it is twisted by the intrinsic Haar
character `HaarModulus.closedInverseHalfCharacter U hU M`. So `m` sends a
class `[v]` to `c(m) • [m v]`, where `c(m) = δ_P(m)^(-1/2)` is a unit of `ℂ`.

## Implemented proof

Write `q = Jacquet.Localization.mk A.representation U 1` for the quotient map,
and `J` for the normalized Jacquet representation of `M`.

**Semidirect factorization and normalization** (`mk_parabolic`). For `p ∈ P`
let `m = h.projection p`, the actual Levi projection. By
`IsSemidirectDecomposition.projection_inv_mul_mem`, `u = m⁻¹ p` lies in `U`,
so `p = m u`. Then `q(p v) = q(m (u v))`. Rewriting with
`Jacquet.Localization.action_mk` writes this as the unnormalized descended
`M`-action of `m` on `q(u v)`. By `Jacquet.Localization.mk_apply_subgroup`
for the trivial character, `q(u v) = q(v)`, so `q(p v) = q(m v)`. By
definition of the twisted action, `J(m)(q v) = c(m) • q(m v)`.
Multiplying by the inverse unit gives

```text
q(p v) = c(m)⁻¹ • J(h.projection p)(q v).
```

Thus every subrepresentation of `J` that contains `q v` also contains
`q(p v)`. The normalization changes each Levi operator only by a nonzero
scalar.

**Finite cover for one vector.** Fix `v`. Smoothness of `A`
(`SmoothRep.isSmooth`) gives an open subgroup `K` fixing `v`. Compactness of
`P \ G` and `Induction.exists_finset_doubleCoset_cover P K` give a finite set
`t ⊆ G` with `G = P t K`. No compactness of `K` is needed. Let `S` be a
subrepresentation of `J` containing `q(i v)` for every `i ∈ t`. Take
`g = p i k` with `p ∈ P`, `i ∈ t` and `k ∈ K`. Then `g v = p (i v)` because
`k v = v`. The displayed formula, with `S` closed under scalars and under
`J`, puts `q(g v)` in `S`. The proof chooses such a finite set `t_v` for each
`v`.

**Finite generators of the Jacquet module.** `Module.Finite.fg_top` gives a
finite set `s` spanning `A` over `ℂ[G]`. Let `y` be the finite union, over
`v ∈ s`, of the classes `q(i v)` with `i ∈ t_v`. Let `N` be the
`ℂ[M]`-span of `y`. Mathlib's `Subrepresentation.ofSubmodule'` turns `N` into
the subrepresentation `S` of `J`. By the previous step, `q(g v) ∈ S` for every
`v ∈ s` and every `g ∈ G`.

**Intersection subrepresentation.** The proof defines the subrepresentation
`C` of `A` whose underlying complex submodule is the intersection over `g ∈ G`
of the inverse images of `S` under the linear maps `q ∘ ρ(g)`. It is
`G`-stable because `ρ(a)(ρ(g)v) = ρ(a g)v`. It contains `s`, so its
group-algebra submodule `C.asSubmodule` contains the `ℂ[G]`-span of `s`,
which is all of `A`. Each class of `J` has the form `q v` by
`Jacquet.Localization.mk_surjective`. Taking `g = 1` in the definition of `C`
puts `q v` in `S`. Hence `N` is everything, and the finite set `y` proves the
`Module.Finite` conclusion. No nonzero vector or nonempty generating set is
needed.

**Corollary.** `finite_of_hasFiniteLength_of_compactQuotient` has the same
hypotheses, except that `A.HasFiniteLength` replaces ambient finite
generation. `SmoothRep.HasFiniteLength` is finite composition length of
`A.representation.asModule` over `ℂ[G]`. Mathlib's
`isFiniteLength_iff_isNoetherian_isArtinian` makes this module Noetherian.
A Noetherian module is finite, so `finite_of_compactQuotient` applies. The
corollary concludes only finite generation of the Jacquet module, not finite
length.

## Provenance and scope

Original source: David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant result is Proposition VI.1.3, printed page 136, PDF page 142.
Renard picks one compact open subgroup `K` fixing all generators. He uses that
`P \ G / K` is finite, so the translates `g_j v_i` generate `V` over `P` and
their images generate `V_N` over `M`. He remarks that the normalization does
not change this.

The implementation follows the same idea with three differences. It works
for the abstract subgroup hypotheses of the target rather than a reductive
parabolic subgroup. Each generator gets its own open stabilizer and
double-coset cover, and the finite covers are combined at the end. The
normalization step is the explicit unit computation of `mk_parabolic`.
Unlike Worker 319's GL-specific proof, this module imports no GL
specialization. It uses only the generic `Aubert.General.Parabolic`
projection and normalized-action definitions, the Jacquet localization API,
the double-coset cover in `Induction.CompactQuotientProof` (both through the
target statement's imports), and `Mathlib.RepresentationTheory.Subrepresentation`.

Compactness of `P \ G` remains a hypothesis. This module does not prove it
for rational points of a reductive group. It also does not prove Jacquet
admissibility, Howe's theorem, finite length of Jacquet modules, or the
separate `DynamicJacquetFiniteLengthStatement`. The target statement pair and
its imports are unchanged.
