# Properness of supplied dynamic parabolic quotients

Author: Worker 712.

`Langlands.GroupScheme.DynamicQuotientProperStatement` is a proposition at an
arbitrary universe `u`. This module states it and does not prove it.

## The proposition

The proposition quantifies over:

- every algebraically closed field `k : Type u`, of any characteristic;
- every actual group scheme `G` over `Spec k` with the existing
  `IsConnectedReductive G`;
- every cocharacter `χ : 𝔾_m → G` defined over `k`;
- every relative scheme `Q` over `Spec k` and relative morphism `q : G.X → Q`.

Here `IsConnectedReductive G` means that `G` is smooth, affine and connected
over `k`, and that its base change to `AlgebraicClosure k` has trivial
unipotent radical. The parabolic `P(χ)` is the existing orbit-extension
subgroup functor `Dynamic.parabolic χ`. A point `g : T → G.X` lies in
`P(χ)(T)` when its conjugation orbit map `T ×_S 𝔾_m → G` extends to
`T ×_S 𝔸¹`.

The supplied quotient must satisfy exactly these hypotheses:

1. The structure morphism `Q.hom : Q → Spec k` is separated, locally of finite
   type and quasi-compact.
2. The underlying scheme morphism `q.left` is smooth, surjective and
   quasi-compact.
3. For every test scheme `Y` over `Spec k` and all `g h : Y → G.X`,
   `g ≫ q = h ≫ q` holds exactly when `g⁻¹ * h ∈ P(χ)(Y)`.

The conclusion is `IsProper Q.hom` for this same supplied `Q`. Properness is
Mathlib's `IsProper`: separated, universally closed and locally of finite
type.

## Reading the hypotheses

The fiber condition gives the orientation of right cosets. Two points have the
same image under `q` exactly when they differ by right multiplication by a
point of `P(χ)`. So the fibers of `q` are the cosets `gP(χ)`, the orbits of
`P(χ)` acting on `G` by right multiplication.

The fiber condition is imposed on every test scheme over `Spec k`, not only on
rational points or on points over field extensions. The test schemes need not
be affine, reduced or of finite type. A condition on rational points alone
would not identify `Q` with the quotient of `G` by `P(χ)`.

The quotient is supplied, not asserted to exist. The proposition applies to
every `Q,q` meeting the hypotheses and concludes properness of that particular
`Q`. A statement asserting only the existence of some proper model, unrelated
to the given `Q`, would be weaker, and it is not what is stated here. The
proposition does not construct a quotient. Existence of a proper quotient with
algebraic local sections is the separate
`DynamicFlagQuotientExistenceStatement`, in
`Langlands/GroupScheme/Dynamic/FlagQuotientStatement`.

The hypotheses on `q` make it an fppf covering whose fibers are the cosets. They
say nothing about properness or closedness of `Q`. The proposition has no
premise `IsParabolicSubgroup`, no regularity or nontriviality condition on `χ`,
and no supplied certificate of properness, closedness or projective closedness.

## Scope

The universe `u` is arbitrary, and the field may have characteristic zero or
any prime characteristic. The trivial cocharacter `χ = 1` is included. Then
every orbit map is constant, so `P(χ) = G` and `q` identifies all points of
`G`. Classically such a quotient is isomorphic to `Spec k`. Every other case
with `P(χ) = G` is included too, for instance a central cocharacter. Rank zero
is included: if `G` has no nontrivial torus, every cocharacter is trivial.

The proposition is restricted to algebraically closed fields, although Milne's
Theorem 25.1 holds over every field. This restriction is the scope needed by the
intended consumer.

## Source correspondence

The classical geometric assertion comes from J. S. Milne, *Algebraic Groups:
The Theory of Group Schemes of Finite Type over a Field* (2017).

- Theorem 25.1, printed p.544 / PDF p.560: for a reductive group `G` and a
  cocharacter `λ`, the subgroup `P(λ)` is parabolic, and every parabolic
  subgroup has this form. Only the first assertion is used here.
- Definition 17.15 and Theorem 17.16, printed p.356 / PDF p.372: a subgroup
  variety `P` of a connected group variety `G` is parabolic when `G/P` is
  complete. Theorem 17.16 says that `P` is parabolic exactly when it contains a
  Borel subgroup.
- Appendix A.75–A.76, printed p.583 / PDF p.599: an algebraic scheme `X` is
  complete when it is separated and, for every algebraic scheme `T`, the
  projection `X × T → T` is closed. A.76(b) says that `X` is complete exactly
  when `X → Spm k` is proper.

Together these give the classical statement that Milne's quotient `G/P(λ)` is
complete, and hence proper over `k`. Milne defines `P(λ)` on `k`-algebras
(printed p.264 / PDF p.280) and shows that it is a smooth algebraic subgroup
when `G` is smooth (13.30 and 13.33). The Lean statement uses instead the
Library orbit-extension functor `Dynamic.parabolic χ` on all test schemes.

The Lean proposition is therefore derived, not a literal transcription of
Theorem 25.1. A proof must compare the supplied smooth surjective quotient
`Q,q` with Milne's quotient `G/P(χ)`, and relate `Dynamic.parabolic χ` to the
source's `P(χ)`. Both comparisons are proof obligations that 25.1 does not
state.

Milne's printed proof of Theorem 25.1 reduces to an algebraically closed field
and chooses a maximal torus `T` with `λ ∈ X_*(T)`. If `λ` is regular, Theorem
21.29 (printed p.433 / PDF p.449) shows that `P(λ)` is a Borel subgroup. If
not, the proof picks a regular `λ'` near `λ` with `P(λ) ⊇ P(λ')`, so `P(λ)`
contains a Borel subgroup and is parabolic by 17.16. This route through 21.29,
that regular cocharacters give Borel subgroups, is not available to the
intended independent proof of this proposition. The statement takes none of
`RegularCocharacterBorelStatement`, `ParabolicDynamicStatement`,
`RankOneSolvableObstructionStatement` or `RankOneBorelDynamicStatement`, nor a
proof of any of them, as an input or dependency. Its imports are the dynamic
subgroup definitions, the definition of reductivity and Mathlib's
morphism-property files.

The registered original is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The registered author's errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read in full. Its
Chapter 25 corrections concern 25.6(b), the sketch in 25.7, 25.10, 25.16,
25.19, 25.24, 25.27 and 25.66–25.69. None alters Theorem 25.1. It has no entry
for printed pp.356, 433 or 583.

## Status and use

This proposition is a geometric prerequisite for the independent rank-one
positive-root argument for `RankOnePositiveRootUniquenessStatement`. It is
distinct from `ParabolicSubgroupQuotientProperStatement` in
`Langlands/GroupScheme/HomogeneousQuotientStatement`. That proposition holds
over all fields, does not assume reductivity, and takes the geometric
`IsParabolicSubgroup` as premise. The existing module
`Langlands/GroupScheme/ProjectiveQuotientEmbedding` descends a projective orbit
map through a supplied quotient by a line stabilizer. The descended map is a
monomorphism, and it is a closed immersion only under the explicit hypothesis
that `Q` is proper. It does not prove this proposition.

Publishing this statement asserts no Lean proof. It establishes neither the
properness of any quotient nor any consumer result.
