# Integral points over a henselian valuation ring

Author: Worker 105.

This module states Corollary 5.7 of Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed p.16, with its scope corrected. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. It contains five
Prop-valued statements and no proofs.

Conrad's Corollary 5.7 reads: "Let `X` be a (quasi-separated) algebraic space locally
of finite type over the valuation ring `R` of a field `k` equipped with a nontrivial
non-archimedean absolute value, and assume that `R` is henselian. The subset `X(R)` in
`X(k)` is open and closed, and if `k` is locally compact and `X` is of finite type over
`R` then `X(R)` is quasi-compact."

The openness and quasi-compactness claims are stated as Conrad gives them. The
closedness claim is false in this generality (see "Scope correction" below). Here it is
stated for separated spaces of finite type, and two further statements record that
neither hypothesis can be dropped.

## Objects

Throughout, `K : Type u` is a nontrivially normed field and `O : Subring K` is a subring
with `x ∈ O ↔ ‖x‖ ≤ 1` for all `x : K`, so `O` is the closed unit ball of `K`. The
algebraic spaces are the Library's actual algebraic spaces
`X : AlgebraicSpace (Spec (CommRingCat.of O))` from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`. All predicates are published
definitions.

- `HenselianLocalRing O` is Mathlib's henselian local ring: `O` is local, and every
  monic polynomial over `O` with a root modulo the maximal ideal, at which its
  derivative is a unit, has a root in `O` lifting it.
- `IsQuasiSeparated X` and `IsSeparated X` (from `RingPoints.lean`) say that the
  diagonal of `X` over `Spec O` is representable with quasi-compact represented
  projections, respectively a representable closed immersion.
- `LocallyOfFiniteTypeOverBase X` (from `StructuralAtlasGeometry.lean`) says that `X`
  has a surjective étale atlas by an actual scheme that is locally of finite type over
  `Spec O`.
- `FiniteTypeOverRing O X` (from `Langlands/Global/AdelicSpaceLevelPointsStatement.lean`)
  says that `X` has such an atlas that is locally of finite type and quasi-compact over
  `Spec O`. For a quasi-separated space this is finite type over `Spec O`: the space is
  quasi-compact and locally of finite type.
- `RingPoints O X A` (from `RingPoints.lean`) is the set `X(A)` of `A`-valued points
  for an `O`-algebra `A`. `RingPoints.changeRing φ` is the map `X(A) → X(B)` induced by
  an `O`-algebra map `φ : A → B`. The inclusion `O → K` is `Algebra.ofId O K`.
- `baseChange (Spec.algebraMap O K) X` (from `SpaceBaseChange.lean`) is the generic fibre
  `X_K`, the base change along `Spec K ⟶ Spec O`. `baseChangeRingPointsEquiv O K K X` is
  the identification `X_K(K) ≃ X(K)`.
- `etaleChartTopology K Y` (from `EtaleChartTopology.lean`) is the strongest topology
  on `Y(K)` making every map `U(K) → Y(K)` continuous, for étale maps `U → Y` from actual
  schemes of finite type over `K`, with the scheme point topology on `U(K)`. This is the
  topology that Conrad constructs in the proof of Proposition 5.4.

Each statement uses the map `ι : X(O) → X_K(K)` given by

`ι x = (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K) x)`.

It views an `O`-point as a `K`-point and then as a rational point of the generic fibre.
Every topological assertion is about the range of `ι` in `X_K(K)`, with
`etaleChartTopology K X_K` on `X_K(K)`.

## The statements

Each statement begins: for every `K` and `O` as above with `HenselianLocalRing O`, and
every algebraic space `X` over `Spec O`.

- `HenselianIntegralPointsOpenStatement`: if `IsQuasiSeparated X` and
  `LocallyOfFiniteTypeOverBase X`, then the range of `ι` is open.
- `HenselianIntegralPointsClosedStatement`: if `IsSeparated X`, then `ι` is injective.
  If moreover `FiniteTypeOverRing O X`, then the range of `ι` is closed.
- `HenselianIntegralPointsCompactStatement`: if `K` is a locally compact space,
  `IsQuasiSeparated X` and `FiniteTypeOverRing O X`, then the range of `ι` is compact
  (`IsCompact`, i.e. quasi-compact; no separation axiom is claimed).
- `HenselianIntegralPointsNotClosedOfFiniteTypeStatement`: for every such `K` and `O`
  there is an `X` with `IsQuasiSeparated X` and `FiniteTypeOverRing O X` whose range of
  `ι` is not closed.
- `HenselianIntegralPointsNotClosedOfSeparatedStatement`: for every such `K` and `O`
  there is an `X` with `IsSeparated X` and `LocallyOfFiniteTypeOverBase X` whose range of
  `ι` is not closed.

## Relation to the source

- **The valuation ring.** Conrad's `R` is the valuation ring of `k` for a nontrivial
  non-archimedean absolute value. Here the absolute value is the norm of a nontrivially
  normed field. Its closed unit ball is required to be a subring `O`. This forces the
  norm to be non-archimedean: for `‖y‖ ≤ ‖x‖` with `x ≠ 0`, both `1` and `y / x` lie in
  `O`, hence so does `1 + y / x`, and so `‖x + y‖ ≤ ‖x‖`. Conversely, for a
  non-archimedean absolute value the closed unit ball is a subring, and it is exactly
  Conrad's valuation ring. "`R` is henselian" is the henselian property of the local
  ring `R`, which is `HenselianLocalRing O`.
- **`X(k)` and its topology.** Conrad writes `X(k)` for an algebraic space over `R`. Its
  topology is that of Proposition 5.4 on the generic fibre `X_k` over `k`. Here this is
  `etaleChartTopology K X_K` on `X_K(K)`. Conrad's proof of Proposition 5.4 (printed
  p.15) claims that this topology has all the properties of Proposition 5.4. That claim
  is stated separately as `EtaleChartTopologyAdmissibleStatement`. Together with the
  uniqueness in Proposition 5.4, it identifies the étale-chart topology with Conrad's
  topology. The generic fibre stays quasi-separated and locally of finite type
  (`IsQuasiSeparated.baseChange` and `HasAtlasProperty.baseChange` in
  `SpaceBaseChange.lean`).
- **"The subset `X(R)` in `X(k)`."** The map `X(R) → X(k)` is injective when `X` is
  separated. Injectivity can fail without separatedness: take two copies of `A^1_R`
  glued along their common generic fibre. So the statements speak of the range of `ι`.
  The closedness statement, which is stated only for separated `X`, also asserts
  injectivity.
- **Locally compact `k`.** This is `LocallyCompactSpace K` for the norm topology. "Of
  finite type over `R`" is `FiniteTypeOverRing O X`, together with the standing
  quasi-separatedness of Section 5 (printed p.13).

The ordering of hypotheses, the names, and the split into five statements are derived
here.

## Scope correction

Conrad's closedness proof uses an étale scheme cover `U → X` such that `U(R) → X(R)` and
`U(k) → X(k)` are surjective. It then asserts that "the full preimage of `X(k) − X(R)`
in `U(k)` is `U(k) − U(R)`". This fails: a `k`-point of `U` can map into the image of
`X(R)` without extending to an `R`-point of `U`. Already for `X = Spec R`, take
`U = Spec R ⊔ Spec k`. Here `Spec k → Spec R` is an open immersion. Then `X(k) − X(R)`
is empty, but `U(k) − U(R)` contains the `k`-point of `Spec k`. The conclusion fails as
well. The counterexamples below are derived here. They are not in the source, and they
are what the two `NotClosed` statements assert to exist. In both, `π ∈ O` has
`0 < ‖π‖ < 1`, which exists because the norm is nontrivial. Since `O` has rank one,
`O[1/π] = K`, so the generic fibre `Spec K` is open in `Spec O`.

- **Quasi-separated of finite type, not separated.** Let `c ∈ K` with `‖c‖ > 1`. Glue
  `X₁ = Spec O[t]` and `X₂ = Spec O[s]` along the generic-fibre opens
  `Spec K[t, 1/t] ⊆ X₁` and `Spec K[s, 1/(s − c)] ⊆ X₂`, via `s = c + t`. The
  intersection is affine, so `X` is quasi-separated. It is covered by two affines of
  finite type over `O`. Every `O`-point of `X` factors through `X₁` or `X₂`, since
  `Spec O` is local. So the range of `ι` is `{t ∈ O} ∪ {s ∈ O}`. The points `t = π^n`
  lie in the range. In the chart `X₂(K) = K` they are `s = c + π^n`, which tend to
  `s = c`. That point is not in the range, since `c ∉ O` and it does not lie in `X₁`.
- **Separated and locally of finite type, not quasi-compact.** For `j ≥ 1` let
  `X_j = Spec O[u_j]` with `u_j = (t − π^j)/π^{j+1}`, so the generic fibre of `X_j` is
  `Spec K[t] = A^1_K`. Glue all `X_j` along their common generic fibre. For `j < k`, the
  constant `u_j − π^{k−j} u_k = (π^k − π^j)/π^{j+1}` has norm `‖π‖^{-1} > 1`. So
  `O[u_j, u_k] = K[t]`, which makes `X` separated. The range of `ι` is the union of the
  pairwise disjoint discs `‖t − π^j‖ ≤ ‖π‖^{j+1}` in `A^1(K) = K`. It accumulates at
  `t = 0`, which lies in none of them.

Why closedness is expected for separated `X` of finite type: Nagata's compactification
theorem for algebraic spaces (Conrad–Lieblich–Olsson, cited by Conrad as [CLO]) gives an
open immersion `X ⊆ X̄` into a proper algebraic space over `O`. Then `X̄(O) = X̄(K)`.
To see this, lift a `K`-point by Chow's lemma to a point of a projective `O`-scheme over
a finite extension `K'`. That point extends over the valuation ring `O'` of `K'` for
the absolute value extending that of `K`, which is unique because `O` is henselian.
It then descends to `O` by the fpqc sheaf property,
using separatedness and the injectivity of `O' ⊗_O O' → K' ⊗_K K'`. A point of `X(K)`
outside the range of `ι` extends to an `O`-point of `X̄` with special point in
`X̄_s ∖ X_s`. Take an affine étale chart of `X̄` with an `O`-point lifting this
extension, which exists since `O` is henselian. The chart points with the same reduction then give an
open neighbourhood disjoint from the range. This is a proof sketch only. No proof is
part of this module.

## Not stated here

- The paragraph after Corollary 5.7 (printed p.17) applies it to the topology on
  `X_S(A_{F,S})` for separated spaces of finite type over `O_{F,S}`, as in Theorem 3.6.
  That application is not stated here.
- Conrad's proofs of openness (étale charts with `R`-point lifts, using that `R` is
  henselian) and of quasi-compactness (finitely many rational points of the special
  fibre over the finite residue field) are proof material. They are not stated here.
