# Finite length under the actual normalized parabolic functors

Author: Worker 270, for task 58159589 (objective by Worker 320). This module
declares three proposition definitions and five compilation-checked
`example`s. It declares no theorem and proves neither clause. A proof is a
separate later task.

## The declarations

Throughout, `p` is a prime, `F : PadicField.{uF} p` is an arbitrary finite
extension of `ℚ_p`, and `T : F.TopologicalData` is an arbitrary supplied
local-field realization. The only topology installed is `letI := T.topology`
on `F.Carrier`. It is not specialized to `canonicalTopologicalData`. All three
declarations live in namespace `Langlands.Parabolic` and take exactly the outer
arguments `{p} [Fact p.Prime] F T`.

- `NormalizedInductionFiniteLengthStatement.{uF, uV} F T` says: for every
  `n : ℕ`, every `B : GeneralLinear.BlockShape n` and every
  `A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`,
  `A.HasFiniteLength → ((T.normalizedParabolicInductionFunctor B).obj A).HasFiniteLength`.
- `NormalizedJacquetFiniteLengthStatement.{uF, uV} F T` says: for every
  `n : ℕ`, every `B : GeneralLinear.BlockShape n` and every
  `A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)`,
  `A.HasFiniteLength → ((T.normalizedJacquetFunctor B).obj A).HasFiniteLength`.
- `NormalizedParabolicFiniteLengthStatement.{uF, uV} F T` is the conjunction
  of the two clauses at the same `F`, `T`, `uF` and `uV`. Rank and shape are
  quantified inside each conjunct, so the conjunction keeps only `F` and `T`
  outside. It is the intended exact target of the later proof. Inspection
  reports its level parameters as `[uF, uV]` and its type as `Prop`.

The suggested names were unused in the Library and are adopted unchanged. The
Library already has an unrelated lowercase theorem
`Langlands.Parabolic.normalizedJacquetFiniteLength`. Its name is different, and
it is discussed under *Relation to existing results*.

## The objects and the predicate

All of these are existing Library definitions, reused by name.

- `SmoothRep.{0, uF, uV} ℂ G` is the actual category of complex
  representations of `G` on modules in `Type uV` in which every vector has an
  open stabilizer. No topology, finite dimension, admissibility or central
  character is imposed on the module.
- `SmoothRep.HasFiniteLength A` (`Category/Basic`) is Mathlib's
  `IsFiniteLength ℂ[G]` for `A.representation.asModule`. This is finite
  composition length over the actual group algebra, not finite complex
  dimension. The zero representation has finite length.
- `GeneralLinear n F.Carrier` is `GL_n(F)` with the units-of-matrices topology
  induced by `T.topology`. `B.Levi F.Carrier` is the product over the blocks of
  `GeneralLinear (B.size i) F.Carrier` with the product topology. These
  topologies are definitionally `T.generalLinearTopology n` and
  `T.leviTopology B`, the ones in the types of the two functors. So
  `letI := T.topology` alone makes the clauses typecheck. No other instance,
  such as a topological-group structure, appears in the statement.

## The two functors

**Induction.** `T.normalizedParabolicInductionFunctor B`
(`Induction/Parabolic`) goes from `SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`
to `SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)`. Write
`P = B.parabolic F.Carrier` for the standard parabolic of upper block-triangular
matrices with diagonal blocks of sizes `B.size i`, and `m(p)` for the Levi part
`B.leviProjection F.Carrier p`. The functor sends a smooth representation `σ` of
the Levi to the smooth vectors of the space of functions `f : GL_n(F) → V` with

`f(p g) = δ_P(m(p))^(1/2) • σ(m(p)) (f g)` for all `p ∈ P`,

on which `GL_n(F)` acts by **right translation**, `(g · f)(x) = f(x g)`. This is
the published `normalizedParabolicInduced_covariant` and
`normalizedInducedOf_apply`. Here `δ_P` is the explicit positive block modulus
`T.leviModulus B`, namely
`δ_P(m) = ∏_{i<j} |det m_i|^(n_j) / |det m_j|^(n_i)`, from `Group/GL/BlockModulus`.
Its positive square root is `T.leviHalfModulus B`. The functor uses smooth
induction, not the compactly supported variant.

**Jacquet.** `T.normalizedJacquetFunctor B` (`Jacquet/Parabolic`) goes from
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)` to
`SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)`. It restricts `ρ` to `P` and takes
the coinvariants `V_N` of the actual upper block unipotent radical
`N = B.unipotentRadical F.Carrier`. The Levi acts by

`m · [v] = δ_P(m)^(-1/2) • [ρ(e(m)) v]`,

where `e = B.leviEmbedding F.Carrier` is the block-diagonal embedding. This is
the published `normalizedJacquet_mk`. The twist is the inverse of the
induction half-modulus (`normalizedJacquet_mk_eq_inv_halfModulus`).

Both clauses apply `Functor.obj` of these exact functors. No external tensor
product of block factors, chosen image, formal label or admissible full
subcategory replaces them.

## Scope

- Every rank is included, including `n = 0`, and every block shape, including
  the empty shape. Block sizes are positive, so the empty shape is the only
  shape of rank `0`. Its Levi is the empty product, a trivial group.
- Every smooth representation of finite length is included, in particular the
  zero representation.
- No admissibility, irreducibility, positive rank, central character, tensor
  factorization, finite dimension or finite generation is assumed. Smoothness
  is part of each object. No proof-valued parameter or theorem-bearing
  structure stands in for the assertions.
- Only finite length of the image is concluded. No bound on the length, no
  exactness and no statement about Grothendieck groups is asserted.

## Universe accounting

The field universe `uF` and the carrier universe `uV` are independent. The
coefficient field `ℂ` lies in universe `0`. In the induction clause the input
carrier is in `Type uV` and the output carrier in `Type (max uF uV)`. In the
Jacquet clause both carriers are in `Type uV`.

The published Grothendieck groups `GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier`
and `B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier`
(`Smooth/FiniteLengthGrothendieck`) are built on the saturated carrier
categories `SmoothRep.{0, uF, max uF uV} ℂ` of `GeneralLinear n F.Carrier` and
of `B.Levi F.Carrier`. Substituting `uV := max uF uV` makes the induction output
universe `max uF (max uF uV)`. Lean's universe normalization reduces this to
`max uF uV`. No resizing or finite-dimensional replacement is used. The module
checks this with five `example`s, all for arbitrary `n` and `B` and under
`letI := T.topology`.

1. `T.normalizedParabolicInductionFunctor.{uF, max uF uV} B` has type
   `SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) ⥤ SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)`.
2. `T.normalizedJacquetFunctor.{uF, max uF uV} B` has type
   `SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) ⥤ SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)`.
3. From `h : NormalizedParabolicFiniteLengthStatement.{uF, max uF uV} F T`,
   `⟨h.1 n B, h.2 n B⟩` proves the published `SmoothRep.PreservesFiniteLength`
   (`Smooth/FiniteLengthGrothendieckFunctor`) for both functors. So at this
   universe the clauses are literally those predicates.
4. Given the same `h` and a separately supplied
   `SmoothRep.PreservesFiniteLengthShortExact` hypothesis for the induction
   functor, the published `B.finiteLengthMapToGeneralLinear` gives a `ℤ`-linear
   map `B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ] GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier`.
5. In the same way, with a short-exactness hypothesis for the Jacquet functor,
   `B.finiteLengthMapFromGeneralLinear` gives a `ℤ`-linear map in the opposite
   direction.

Examples 4 and 5 only check that the types fit. The short-exactness inputs are
hypotheses of the examples, not claims of this module. Examples 1, 2, 4 and 5
produce data, so they are marked `noncomputable`.

## Sources and provenance

The statement has derived provenance. For positive rank it specializes
published theorems about finite length and admissibility. The rank-zero case
is an elementary extension.

**Casselman**, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995. Literature ID
`casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`. Printed
page numbers, which agree with the PDF pages; these pages were read:

- §2.4, p.26: `Ind_H^G σ` consists of smooth `f` with `f(hg) = σ(h) f(g)`.
  `G` acts by the right regular representation.
- §3.1, p.32: for a parabolic `P = MN` and smooth `σ` of `M`, normalized
  induction is `i_P^G σ := Ind_P^G(σ δ_P^(1/2))`, where `δ_P` is the modulus
  character `δ_P(mn) = |det Ad_n(m)|`.
- Theorem 3.3.1, p.35: if a smooth `(π, V)` of `G` is finitely generated
  (resp. admissible), then the unnormalized Jacquet module `(π_N, V_N)` is a
  smooth, finitely generated (resp. admissible) representation of `M`.
- Corollary 6.3.8, p.60: for any parabolic `P`, if `σ` is any admissible
  representation of `M` of finite length, then `i_P^G σ` has finite length.
- Theorem 6.3.10, p.60: any finitely generated admissible representation of
  `G` has finite length.

No erratum for this draft was found in the project literature index, the
central-library listing or the public notes.

The admissibility input is the published statement
`Langlands.FiniteLengthAdmissibilityStatement`
(`Smooth/Admissibility/FiniteLengthStatement`). It says that finite-length
smooth representations of `GL_n(F)` and of `B.Levi F.Carrier` are admissible.
Its Markdown cites Bernstein and Zelevinsky (1976), Theorem 4.1, pp.37-38:
finite length is equivalent to admissible plus finitely generated. That
statement is still unproved in the Library. It is cited here for provenance,
not as a proved input.

## Correspondence with the source

- **Groups.** Casselman's field is any locally compact non-archimedean field,
  and `G` is a connected reductive group. Here the field is a finite extension
  of `ℚ_p`, `G = GL_n`, `P` is the standard upper block parabolic of shape `B`,
  and `M` is its block-diagonal Levi. The Library's `B.Levi` is the abstract
  product of the `GL_{n_i}`. It is identified with the block-diagonal subgroup
  through the actual maps `B.leviProjection` and `B.leviEmbedding`.
- **Normalization.** Casselman's condition `L_p f = σ^(-1) δ_P^(-1/2)(p) f` is
  the covariance `f(pg) = δ_P^(1/2)(p) σ(p) f(g)` used here, with right
  translation. The Lean modulus is the explicit block formula. Its equality
  with the Haar modulus `|det Ad_n(m)|` is a separate obligation, neither
  assumed nor needed here. Twisting by a smooth character changes neither the
  invariant subspaces nor admissibility. So finite length of the image does
  not depend on which positive character normalizes the functors.
- **Jacquet.** Casselman's `V_N` in Theorem 3.3.1 is unnormalized. The Lean
  functor additionally twists by `δ_P^(-1/2)`, which again preserves finite
  length.
- **Finite length.** Casselman's finite length is finite length of
  `G`-modules, that is, over `ℂ[G]`. This is `HasFiniteLength`.

## Derivation, for explanation only

The following explains why the statement is expected to hold. It is not a
proof, and a later proof may follow another route.

- *Induction, positive rank.* A finite-length `σ` of the Levi is admissible by
  the Levi clause of `FiniteLengthAdmissibilityStatement`. Twisting by
  `δ_P^(1/2)` (explicit or Haar) keeps it admissible and of finite length.
  Corollary 6.3.8 then gives finite length of the induced representation. The
  extra admissibility step makes this a derived specialization, not a verbatim
  instance of Corollary 6.3.8, which assumes admissibility.
- *Jacquet, positive rank.* A finite-length `ρ` of `GL_n(F)` is admissible by
  the GL clause, and finitely generated because a module of finite length is
  Noetherian. Theorem 3.3.1 makes `V_N` admissible and finitely generated.
  Theorem 6.3.10 for `M` gives finite length, and the twist preserves it.
- *Rank zero.* For `n = 0` the only shape is empty. `GL_0(F)`, the parabolic,
  the radical and the Levi are trivial groups, and the half-modulus is `1`.
  Induction of `σ` is then a representation of the trivial group whose space
  is canonically isomorphic to that of `σ`. The Jacquet module is the space
  of `ρ` with no relations. Both statements then reduce to finite length of
  the same space over the trivial-group algebra. This case is not covered by
  the positive-rank source results. It must be proved separately.

## Relation to existing results

- `Langlands.Parabolic.normalizedJacquetFiniteLength`
  (`Classification/FiniteLengthProof`, published) proves for every `T`, rank
  and shape, including rank zero: if `ρ` of `GL_n(F)` is admissible and
  finitely generated over `ℂ[GL_n(F)]`, then `T.normalizedJacquet B ρ` has
  finite length. With the GL clause of `FiniteLengthAdmissibilityStatement`,
  once proved, it yields the Jacquet clause here.
- `Langlands.Classification.AdmissibleFiniteLengthProductPreservation`
  (`Classification/NormalizedProductFiniteLengthStatement`) concerns
  normalized product induction of external families of GL block factors, for
  positive rank, and assumes admissibility. The induction clause here
  instead covers every finite-length smooth representation of the actual
  product Levi, including non-factorized ones and rank zero, with no
  admissibility hypothesis.
- Exactness of both functors is published separately as
  `Parabolic.normalizedInductionExactness` (`Parabolic/InductionExactnessProof`)
  and `Parabolic.normalizedJacquetExactness`
  (`Parabolic/NormalizedJacquetExactnessProof`). It is not restated here.

## Dependencies and what is not claimed

The imports are `Langlands.Representation.Induction.Parabolic`,
`Langlands.Representation.Jacquet.Parabolic` and
`Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor`. The last
one is needed only by the examples. No existing Library file is changed.

This pair proves neither clause. It also does not prove the admissibility
input, Casselman's Corollary 6.3.8 or Theorem 6.3.10 in Lean, exactness,
short-exactness preservation, or descent to Grothendieck groups. It asserts
no length bound, no irreducible basis and nothing about classification.
