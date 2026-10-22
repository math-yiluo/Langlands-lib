# Quasicuspidal prerequisites for cuspidal embedding

Author: Worker 171.

This pair states three future proof targets in `Langlands.CuspidalSupport`.
Every declaration is a proposition definition or abbreviation. No proof of
these assertions, or assumption of their truth, is introduced. The field is
an actual `PadicField.{uF} p`, with prime `p` and compatible topological data
`T`. Its universe `uF` is independent of the representation carrier universe
`uV`.

## Exact declarations

`NormalizedQuasicuspidalEmbeddingTheorem.{uF,uV} F T n` places `0 < n`
inside its proposition body. For every irreducible
`SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)`, it asserts the existence
of an actual `BlockShape n`, an irreducible smooth representation of its
product Levi with carrier in `Type uV`, and an injective intertwining map
into its normalized parabolic induction. The inducing representation satisfies
the published `IsLeviQuasicuspidal` predicate. There is no admissibility
hypothesis or conclusion for either representation in this clause.

The existential and intertwiner expression is the one in
`CuspidalEmbeddingTheorem`, with `IsLeviCuspidal` replaced by
`IsLeviQuasicuspidal` and the source-admissibility conjunct removed. In
particular, induction uses `Induction.smoothInduced`, inflation through the
actual `B.leviProjection F.Carrier`, and the actual positive character
`T.parabolicHalfModulus B`. Its action is right translation on covariant
functions. The induced carrier may lie in `Type (max uF uV)`, so the
embedding is an actual intertwining map between potentially different
carrier universes. The Levi need not be proper.

`IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF,uV} F T B` has
implicit rank `n` and an arbitrary `B : BlockShape n`. Every irreducible
smooth complex representation of `B.Levi F.Carrier` in carrier universe
`uV` is admissible if it is `IsLeviQuasicuspidal`. That predicate tests the
actual unipotent coinvariant quotient for each proper standard refinement.
Admissibility is the existing all-open-subgroups condition. Neither a
central character nor countability, finite generation, finite length, or
admissibility is an input.

`ZeroRankCuspidalEmbeddingTheorem.{uF,uV} F T` abbreviates
`CuspidalEmbeddingTheorem.{uF,uV} F T 0` definitionally. It retains both
the admissibility conclusion and the cuspidal inducing data of that target.

`CuspidalEmbeddingPrerequisites.{uF,uV} F T` conjoins the first target
for every rank, the second for every rank and block shape, and the third.
The positivity implication remains inside the first target. Each individual
declaration is available independently for a future proof.

## Original sources

The retained originals were read directly on 2026-10-21. No corresponding
source errata note was present in the current Library.

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F), where F is a non-Archimedean local field*, Russian Mathematical
  Surveys 31:3 (1976), 1–68. Literature ID:
  `bernstein-zelevinsky-1976-representations-gln`; PDF SHA-256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Chapter II, §§3.12–3.13 (printed/PDF pp.32–33), Proposition 3.19
  (p.34), Theorem 3.21 (pp.34–35), Theorem 3.25 and Lemma 3.26
  (pp.35–36). Supporting passages: §§2.1 and 2.6 (pp.15–16),
  §2.9 (p.17), §§2.21–2.22 and 2.26 (pp.21–23), §2.41 (p.26),
  and §§3.1–3.6 (pp.28–30).
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
  reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
  Literature ID: `bernstein-zelevinsky-1977-induced-i`; PDF SHA-256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  §§2.2–2.5, printed pp.446–447 / PDF pp.7–8, with the normalized
  covariance convention in §1.8(a), printed p.444 / PDF p.5, and the
  smooth representation and character conventions in §§1.2–1.5,
  printed p.443 / PDF p.4.

The 1976 source's `Alg` means smooth complex representations. Its
`G_α` is already a product of general linear groups (§§3.3–3.4), so the
Levi admissibility assertion does not require decomposing an irreducible
product representation as a tensor product. Finite p-adic extensions with
the specified compatible topology specialize its nonarchimedean local
fields. Ordered positive block shapes and their standard refinements
represent the partitions and subpartitions in the sources.

## Embedding and the derived normalization

BZ76 Proposition 3.19 is an **unnormalized** embedding assertion:
§3.12 uses induction of the inflated Levi action without a half-modulus.
Its proof chooses a minimal refinement with nonzero Jacquet module.
Transitivity (§3.13(c)) makes that module quasicuspidal. An irreducible
representation is cyclic; preservation of finite generation (§3.13(e))
and the irreducible quotient lemma (§2.6) produce an irreducible quotient.
Exactness (§3.13(a)) preserves quasicuspidality in that quotient.
Reciprocity (§3.13(b)) gives a nonzero map into induction, and
irreducibility makes it injective. These are source proof steps, not
proofs implemented here. The Jacquet module and its quotient can be formed
in the source carrier universe, explaining the same `uV` for inducing
data without imposing a relation between `uV` and `uF`.

For the normalized variant stated here, let `ρ` be those unnormalized
inducing data and let `χ = T.leviHalfModulus B`. Replace `ρ` by
`σ = χ⁻¹ ⊗ ρ`, on the same carrier. Since
`T.parabolicHalfModulus B = χ ∘ B.leviProjection F.Carrier`, twisting
the inflated `σ` by the positive half-modulus cancels the inverse twist
and recovers the original covariance action. Thus the original embedding
has exactly the required normalized target after this identification.
BZ76's compactly supported induction equals its smooth induction for this
parabolic, since the quotient is compact (§3.13(b), using §3.6).

The half-modulus has open kernel, as already proved in
`Langlands.Group.GL.BlockModulus`; intersecting vector stabilizers with
that kernel preserves smoothness of the twist. Twisting by invertible
scalars leaves invariant subspaces unchanged and hence preserves
irreducibility. On any refined unipotent radical in the Levi, each original
block determinant is one. The block determinant formula for `χ` therefore
gives `χ = 1` there. The unipotent actions and their coinvariant quotients
are unchanged, preserving quasicuspidality. These observations justify the
derived normalized statement; their required Lean implementations remain
future proof obligations. BZ77 §§1.8 and 2.3 fix this normalized convention,
and §2.5 is the intended final cuspidal embedding and admissibility theorem.

## Admissibility without a circular argument

BZ76 Theorem 3.25 asserts admissibility of every irreducible smooth
representation of `G_α`; the quasicuspidal clause here is a restriction
of that assertion for nonempty shapes. For a future proof, its
quasicuspidal case can be used directly, without the preliminary reduction
through Proposition 3.19 and induction admissibility. Harish-Chandra's
Theorem 3.21 says that restriction to the open subgroup `G_α⁰` is a finite
representation, where “finite” concerns compactly supported matrix
coefficients, not finite vector-space dimension. Lemma 3.26 gives a
finite direct sum of irreducible representations on that restriction.
Each summand is finite, hence admissible by §2.41. The finite sum is
admissible; for any open subgroup `K` of `G_α`, its fixed vectors embed
in the fixed vectors for the open subgroup `K ∩ G_α⁰`. This yields
the all-open-subgroups admissibility used in Lean.

Lemma 3.26 derives scalar central action through Schur's lemma and uses
the finite-index restriction lemma §2.9 and §3.20(b). Central character
data are not hypotheses of Theorem 3.25 or of our target. Likewise,
countability properties of these local groups used in the source argument
do not impose countability of the representation carrier.

## Elementary boundary and assembly

The sources above concern positive-rank groups. For `n = 0`, positivity
of block sizes forces an empty shape. Its product Levi and `GL_0` are
trivial groups. An irreducible complex representation of a trivial group
is one-dimensional: the span of a nonzero vector is invariant and must
be the whole space. It is therefore admissible, and the empty Levi has
no proper standard refinement. This explains the empty-shape case of
the admissibility target. Identity induction from the full trivial group,
whose half-modulus is one, supplies the rank-zero embedding. These are
elementary derived boundary arguments, not assertions quoted from the
positive-rank literature and not proofs supplied by this pair.

For positive rank, applying Levi admissibility to the inducing data in
the first clause upgrades `IsLeviQuasicuspidal` to `IsLeviCuspidal`.
Admissibility of the induced representation is the separate, already
published `Langlands.Parabolic.NormalizedInductionAdmissibilityClause`
in `Langlands.Representation.Parabolic.NormalizedInductionStatement`;
it is reused by that name and not restated here. Restricting invariant
vectors along the injective intertwiner then gives admissibility of the
source. A future proof of the parent target still needs those results
and this elementary transfer. The rank-zero target handles the remaining
case. The aggregate in this pair packages only the three new targets.
