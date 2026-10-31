# Weyl transport along block-Weyl cosets, and admissibility of transported filtrations

Author: Worker 285. The design was coordinated with Worker 240 on task
`18476e24-f842-458b-9a71-0fb03f270b2c`. Worker 240 later replaced a local
copy of the transport-admissibility lemma with the published one (see below).

This module proves internal lemmas in namespace `Langlands.CuspidalSupport`.
It works with the actual product Levis `B.Levi F` and `C.Levi F` of two block
shapes `B` and `C` of the same size `n`. It also uses the Library's Weyl
transport `transport B C w hw`, which precomposes a source-Levi
representation with the inverse of `leviConjugation B C w hw`. Carriers are
complex vector spaces in independent universes. No carrier is assumed
finite-dimensional.

## Statements

Fix `b` in the source block-Weyl group `blockWeyl B`, the permutations
preserving every block of `B`.

- `blockWeylLeviElement B hb : B.Levi F`. This is the Library projection
  `B.leviProjection` of the permutation matrix of `b`. That matrix lies in
  the standard parabolic of `B` by the published
  `permutation_mem_parabolic_of_mem_blockWeyl`. The field `F` is arbitrary.
- `leviConjugation_symm_mul_blockWeyl`. Assume `v` and `v * b` both
  conjugate the Levi of `B` onto the Levi of `C`. Then, for every `m` in the
  target Levi, the inverse conjugation by `v * b` sends `m` to
  `β⁻¹ * (inverse conjugation by v)(m) * β`. Here `β` is
  `blockWeylLeviElement B hb`.
- `transportBlockWeylEquiv`. Under the same hypotheses, and for every
  representation `ρ` of the source Levi, there is an actual equivalence of
  representations from `transport B C (v * b) hw ρ` to
  `transport B C v hv ρ`. Its linear map is `ρ β`, with inverse `ρ β⁻¹`.
- `exists_minimal_transport_equiv`. Assume every conjugating permutation `w`
  can be written `w = v * b`, where `v` is a minimal conjugating
  permutation and `b` lies in `blockWeyl B`. If `ρ` and `σ` are associated
  (`RepresentationsAssociated`), then some minimal conjugating permutation
  `v` has `transport B C v ρ` equivalent to `σ`.
- `exists_minimal_transport_equiv_of_associated`. The same conclusion with
  no coset hypothesis, over an arbitrary field `F` and every rank `n`
  (including `n = 0`): if `ρ` and `σ` are associated, some minimal
  conjugating permutation `v` has `transport B C v ρ` equivalent to `σ`.

For a field `F` with a topology making it a topological ring:

- `isAdmissible_of_transportFiltration`. Let `A` be a `Rep ℂ (C.Levi F)` with
  smooth action and a finite filtration `s : ObjectRepFiltration A r`. Let
  each graded piece of index `i` be equivalent to the transport of a single
  admissible `ρ` along a conjugating permutation `e i`. Then `A` is
  admissible.

## Implemented proofs

`leviConjugation_symm_mul_blockWeyl`. Let `P_b` be the permutation matrix of
`b`, viewed in the parabolic of `B`. The two sides are first compared after
the Library inclusion `B.leviInParabolic` of the Levi into the parabolic.
The published `leviConjugation_symm_embedding` identifies the inverse
conjugation by `w` with matrix conjugation by the inverse permutation matrix
of `w`. The permutation matrix map is multiplicative, so the matrix for
`v * b` is the matrix for `v` times `P_b`. The two parabolic elements
therefore have the same underlying matrix. Applying the group homomorphism
`B.leviProjection` gives the claim, since `leviProjection_section` says that
projection undoes `leviInParabolic`.

`transportBlockWeylEquiv`. The two inverse identities `ρ β ∘ ρ β⁻¹ = id` and
`ρ β⁻¹ ∘ ρ β = id` give the linear equivalence. To check equivariance at `m`,
rewrite the inverse conjugation by `v * b` with the previous lemma. Then
`ρ` is multiplicative, and `ρ β` cancels `ρ β⁻¹` on the left.

`exists_minimal_transport_equiv`. Association gives `w`, the proof `hw` that
`w` conjugates the Levis, and an equivalence `e` from the transport along
`w` to `σ`. The coset hypothesis writes `w = v * b`. The required
equivalence is the inverse of `transportBlockWeylEquiv` composed with `e`.
`exists_minimal_transport_equiv_of_associated` feeds the existence part of
the published field-general `minimalConjugatingCosets` (module
`Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof`) to
this lemma.

`isAdmissible_of_transportFiltration`. Each graded piece is admissible. This
follows from the equivalence with a transport and the published
`isAdmissible_of_equiv`, together with the published
`isAdmissible_transport` (module
`Langlands.Representation.CuspidalSupport.AssociationReduction`): Weyl
transport of an admissible representation is admissible. The lemma
`isAdmissible_of_objectRepFiltration` from module
`Langlands.Representation.Smooth.Admissibility.Extension` concludes.

## Provenance

These are internal lemmas for the proof of Bernstein–Zelevinsky 1977,
*Induced representations of reductive p-adic groups I*, Theorem 2.9(a),
implication (i)⇒(ii) (printed p. 448; proof in §2.15(2), printed p. 449).

- §2.6 (printed p. 447) calls `ρ` and `ρ'` associated if `ρ' ≅ w(ρ)` for some
  `w` in `W(M, N)`. Corollary 2.13(c) indexes the graded pieces of the
  geometric-lemma filtration by `W(M, N)/W_M`. The lemma
  `transportBlockWeylEquiv` is the formal reason a representative of the
  coset `w W_M` may be chosen: for `b` in `W_M`, `w b(ρ) ≅ w(ρ)`, because
  `b(ρ)` is conjugation of `ρ` by an element of `M`. BZ77 uses this
  implicitly. The coset parametrization itself is the published
  `minimalConjugatingCosets`, which proves `MinimalConjugatingCosetsTheorem`;
  only its existence part is used here.
- BZ77 obtains admissibility of the Jacquet module of an induced cuspidal
  representation from 2.3(e) (printed p. 446). The lemma
  `isAdmissible_of_transportFiltration`, with the published
  `isAdmissible_transport`, derives it instead from the geometric-lemma
  filtration with transported graded pieces.
