# The cuspidal-support grading of the graded Grothendieck ring

Module `Langlands.Representation.Aubert.SupportGrading`, namespace
`Langlands.Aubert.SupportGrading`.

This is a helper module for the injectivity half of
`Langlands.Aubert.SegmentPolynomialComparisonStatement` (Zelevinsky 1980,
Corollary 7.5). The construction is internal: Zelevinsky proves 7.5 through the
classification, not through a support grading. The representation-theoretic
inputs are published Library theorems:

- existence and uniqueness of supercuspidal supports for `n > 0`
  (Zelevinsky 1980, 1.10; `glSupercuspidalEmbedding`,
  `glSupercuspidalSupportUniqueness`);
- every irreducible subquotient of a binary product `X × Y` has support
  `s + t` when `s`, `t` are supports of `X`, `Y`
  (`PadicField.TopologicalData.binaryProductConstituentSupport`);
- a segment socle embeds in the cuspidal product of the members of its segment
  (`Classification.SegmentSocleProductCaseTwo.embedsCuspidal_socle`);
- an irreducible representation of `GL_0` is one-dimensional and isomorphic to
  the binary unit (`Classification.SegmentHeadSupport.finrank_eq_one_of_isIrreducible`,
  `Classification.SegmentProductOrderedAssembly.nonempty_iso_unit`,
  `emptyProductUnitIso`);
- the factor map and composition factors of the exact Grothendieck group
  (`SmoothRep.IrreducibleGrothendieckProof.factorMap`,
  `realize_comp_factorMap`, `compositionFactors_irreducible`,
  `SmoothRep.IrreducibleOperator.mem_support_compositionFactors_iff_isSubquotient`).

Throughout, `A = GradedGrothendieckGroup F T` carries the ring structure
`gradedInductionRing F T hx hl`, cuspidal data and segments live in the universe
`max uF uV` (as for `gradedSegmentSocle`), and `G = CuspidalDatum →₀ ℤ` is the
free abelian group on cuspidal data. `A[G]` is `AddMonoidAlgebra A G`, and
`e^g = single g 1`.

## Supports in every rank (section `Support`)

- `eq_zero_of_isSupercuspidalSupport_rankZero`: a supercuspidal support of a
  representation of `GL_0` is the empty multiset. The ranks of a support sum to
  `0` (`IsSupercuspidalSupport.sum_rank`) and every cuspidal datum has positive
  rank.
- `exists_isSupercuspidalSupport`: every irreducible `π` of `GL_n(F)` has a
  supercuspidal support, for all `n`. For `n > 0` this is
  `glSupercuspidalEmbedding`. For `n = 0`, `π` is one-dimensional, hence
  isomorphic to the binary unit, which is isomorphic to the empty cuspidal
  product. So `π` is a subquotient of the empty cuspidal product and `0` is a
  support.
- `isSupercuspidalSupport_unique`: two supports of an irreducible `π` are
  equal, for all `n`: by `glSupercuspidalSupportUniqueness` for `n > 0` and by
  the rank-zero lemma for `n = 0`.
- `isSupercuspidalSupport_supercuspidalSupport'`, `supercuspidalSupport_eq`,
  `supercuspidalSupport_eq_of_iso`: the Library's chosen support
  `T.supercuspidalSupport π` is a support of every irreducible `π`, equals any
  given support of `π`, and is invariant under isomorphism.
- `classSupport F T n`: the support of an irreducible class of `GL_n(F)`, the
  descent of `T.supercuspidalSupport` to isomorphism classes;
  `classSupport_irreducibleIsoClass` evaluates it on the class of `π` (by `rfl`).
- `supportDegree T s`: the image `∑_{ρ ∈ s} e_ρ` of a multiset in
  `CuspidalDatum →₀ ℤ`, with `supportDegree_zero`, `supportDegree_add`,
  `supportDegree_singleton`.
- `cuspidalContent_eq_map_range`: the cuspidal content of `Δ` is
  `{Δ.member i : i < Δ.length}`.
- `cuspidalContent_dropLastNonempty`: for `1 < Δ.length`, the content of `Δ` is
  the content of `Δ⁻ = Δ.dropLastNonempty h` (same beginning, one element fewer)
  plus `{Δ.last}`; `cuspidalContent_of_length_eq_one`: for length one the
  content is `{Δ.last}`.
- `supercuspidalSupport_segmentSocleObject`: the support of the chosen segment
  socle `segmentSocleObject F T Δ` is the cuspidal content of `Δ`.

## Generation by irreducible classes (section `Generation`)

- `induction_irreducible`: a property of elements of the exact Grothendieck
  group of `GL_n(F)` that holds for `0`, is closed under sums and negatives, and
  holds for the class of every irreducible representation, holds everywhere.
  Proof: every `x` equals `realizeIrreducibles (factorMap x)`
  (`realize_comp_factorMap`); induct over the finitely supported vector
  `factorMap x`, and on each single term `single c z` induct over the integer
  `z`.

## The support twists (section `Twist`)

For an integer `s`:

- `rankSupportTwist F T hx hl s n`: the additive map from the Grothendieck
  group of `GL_n(F)` to `A[G]` sending `x` to the sum, over the irreducible
  classes `c` with coefficient `z_c ≠ 0` in `factorMap x`, of
  `single (s · supportDegree (classSupport c)) (gradedInclusion n (realizeIrreducibles (single c z_c)))`
  (`rankSupportTwist_apply`). It is built from `Finsupp.liftAddHom`, so on an
  irreducible class it is `[π] ↦ e^{s · supp π} [π]`.
- `rankSupportTwist_of_support`: if every irreducible subquotient `D` of a
  finite-length `M` has support `t`, then the twist of `[M]` is
  `single (s · supportDegree t) (gradedInclusion n [M])`. Proof: `factorMap [M]`
  is `compositionFactors M`, whose support consists of classes of irreducible
  subquotients of `M`; each term of the sum has degree `s · supportDegree t`,
  and the remaining sum realizes `[M]`.
- `rankSupportTwist_irreducible`: the twist of the class of an irreducible `π`
  is `single (s · supportDegree (supp π)) (gradedInclusion n [π])`.
- `rankSupportTwist_binaryProduct`: the twist of `binaryProductK0 x y` is the
  product of the twists of `x` and `y` in `A[G]`. Proof: by
  `induction_irreducible` in both arguments it suffices to treat irreducible
  `X`, `Y`. The class of the product is the class of `X × Y`
  (`binaryProductK0_classes`), and every irreducible subquotient of `X × Y` has
  support `supp X + supp Y` (`binaryProductConstituentSupport` and uniqueness),
  so `rankSupportTwist_of_support` applies. The right side is
  `single (s · deg X) [X] * single (s · deg Y) [Y] = single (s · deg X + s · deg Y) ([X] [Y])`,
  and `[X] [Y]` is the graded class of `X × Y` (`gradedMultiplication_homogeneous`).
- `supportTwistAddHom`: the direct-sum extension of the rank twists,
  `supportTwistAddHom_inclusion` its value on a homogeneous element.
- `supportTwistAddHom_one`: it sends `1 = gradedUnit` to `1`. The binary unit is
  irreducible (one-dimensional) and its support is empty (rank zero).
- `supportTwistAddHom_mul`: it is multiplicative, by induction over both direct
  sums and `rankSupportTwist_binaryProduct` on homogeneous pieces.
- `supportTwist F T hx hl s`: the resulting ring homomorphism `χ_s : A →+* A[G]`,
  with `supportTwist_apply`.
- `supportTwist_segmentSocle`: `χ_s (gradedSegmentSocle Δ) =
  single (s · supportDegree (Δ.cuspidalContent)) (gradedSegmentSocle Δ)`.

## The expansion (section `Expansion`)

- `untwist F T hx hl`: the ring endomorphism `μ` of `A[G]` with
  `μ (single g a) = χ_{-1}(a) · e^g` (`AddMonoidAlgebra.liftNCRingHom`; `A[G]` is
  commutative).
- `expansion F T hx hl D`: for a ring endomorphism `D` of `A`, the ring
  homomorphism `E = μ ∘ (D applied to coefficients) ∘ χ_1 : A →+* A[G]`.
- `expansion_segmentSocle`: suppose `D ζ(Δ) = ζ(Δ) + y`,
  `χ_{-1}(y) = single (-c) y`, and `supportDegree (Δ.cuspidalContent) =
  c + e_{Δ.last}`. Then `E ζ(Δ) = single 0 ζ(Δ) + single (e_{Δ.last}) y`, where
  `ζ(Δ) = gradedSegmentSocle F T Δ`. Proof: with `d` the degree of the content,
  `χ_1 ζ(Δ) = single d ζ(Δ)`, so
  `E ζ(Δ) = χ_{-1}(ζ(Δ) + y) · e^d = (single (-d) ζ(Δ) + single (-c) y) · e^d`.
- `intCast_eq_zero`: if the integer `c` maps to `0` in `A` then `c = 0`. The
  integer `c` is `c · gradedUnit = gradedInclusion 0 (c · [1])`; the homogeneous
  component shows `c · [1] = 0`, and the factor map sends this to `c` times the
  generator of the class of the unit, whose coefficient is `c`.

## Use

`SegmentPolynomialInjectivity` applies `expansion_segmentSocle` and
`intCast_eq_zero` to the criterion `SegmentEndDerivation.injective_of_endExpansion`,
with `D` the total Bernstein–Zelevinsky derivative.
