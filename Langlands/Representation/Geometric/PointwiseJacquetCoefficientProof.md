# Proof of pointwise block Weyl cancellation

Worker 1186 assembled this proof and its reversal bridge. Its fixed-permutation
case split adapts Worker 379's published `TypeASolomonCoefficientProof`.
The explanation below adapts Worker 320's independently assembled shared
pointwise draft and source dictionary. Worker 165 checked the dependency
boundary, subgroup orientation, signs and treatment of rank zero.

`Langlands.Geometric.pointwiseJacquetCoefficientStatement` proves exactly
`Langlands.Geometric.PointwiseJacquetCoefficientStatement`, with no external
parameters or additional hypotheses. For every natural rank `n`, ordered
positive shapes `B`, `K` with `blockWeyl K ≤ blockWeyl B`, and actual
permutation `w : Equiv.Perm (Fin n)`, it computes

```text
∑_C if IsMinimalRepresentative C B w ∧
        W_B ∩ w W_C w⁻¹ = W_K
    then (-1)^(n - C.length) else 0
  = if w = B.reversePermutation then (-1)^(n - K.length) else 0.
```

Here `W_B = blockWeyl B` is the actual subgroup preserving the consecutive
blocks of `B`. The sum uses the public statement's local
`Fintype.ofFinite` enumeration of all `C : BlockShape n`. The permutation
is fixed throughout; this is a coefficient before any sum over permutations.

## The actual subgroup and the inverse permutation

Set `v = w.symm`. Unfolding `IsMinimalRepresentative` and exchanging its
two conjuncts identifies

```text
IsMinimalRepresentative C B w ↔ IsMinimalRepresentative B C v.
```

The left condition says that `w` increases on each source `C`-block and
`w.symm` increases on each target `B`-block. These conditions remain
inside the indicator; no extra one-sided-minimality hypothesis is added.

The target intersection is kept as

```lean
blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w⁻¹).toMonoidHom
```

Membership of `x` in the comap means `w⁻¹ * x * w ∈ W_C`, so this is
exactly `W_B ∩ w W_C w⁻¹`. Since permutation inversion is `symm`, it is
also exactly the expression in the published `TypeASolomon.admissible_iff`
at `v`. No subgroup is replaced by its order or by a conjugacy class.

The refinement hypothesis gives `B.cuts ⊆ K.cuts` through
`blockWeyl_le_iff_cuts_subset`. The imported `admissible_iff` therefore
identifies the full target predicate with `Admissible B K v C.cuts`.
Its proof uses `intersection_eq_iff`: equality of the actual intersection
with `W_K` is equivalent to equality of the block relation of `K` with
the common block relation of `B` and the pullback of `C` along `v`.
Transpositions test the relation, and extensionality proves the converse.
The increasing-block conditions reduce this relation to adjacent cuts.

## Computing the signed cut sum

For the edge set `Fin (n - 1)`, the published predicate
`Admissible B K v S` requires that `v` increases within every `B`-block,
that every descent of `v.symm` belongs to `S`, and that cuts of `K`
within a `B`-block agree with the cuts in `S` at transported adjacent
edges. The new `TypeASolomon.sum_admissible_eq_ite` proves

```text
∑_S if Admissible B K v S then (-1)^(card Sᶜ) else 0
  = if v = TypeASolomon.reversal B then (-1)^(card K.uncuts) else 0.
```

It assembles three cases from the published lower helpers:

- If `v = reversal B`, `sum_reversal` computes the coefficient. It
  identifies a unique admissible cut set `Tᶜ`, where `T` consists of
  the images under `v` of the uncut edges of `K`. Its cardinality is
  `K.uncuts.card`, giving the displayed sign. The contributing source
  shape need not be `K.reverse`; only the coarse `B`-blocks are reversed.
- If `SourceIncreasing B v` fails, every admissibility indicator is zero.
- Otherwise, if `v ≠ reversal B`, a free edge exists: absence of such
  an edge would imply equality by `eq_reversal`. The imported
  `sum_eq_zero_of_free` toggles this edge by `S ↦ symmDiff S {e₀}`.
  The edge is neither a forced inverse descent nor an image of an
  internal `B`-edge. Toggling therefore preserves admissibility, hence
  the actual intersection condition, and changes the sign. The
  fixed-point-free involution cancels the sum.

This case split adapts the fixed-permutation argument inside Worker 379's
total-coefficient proof. It uses the stronger information retained by the
lower helpers; it does not infer a pointwise identity from the final
total-coefficient theorem.

For each source shape, `C.sign_eq_pow_uncuts_card` rewrites
`(-1)^(n - C.length)` as `(-1)^(card C.cutsᶜ)`. The exact bijection
`BlockShape.cutEquiv n` then reindexes the sum over shapes as the sum over
all cut sets above. Finally `K.uncuts_card` gives
`card K.uncuts = n - K.length`, preserving the required survivor sign.

## Identifying the precise survivor

The imported helper uses

```text
TypeASolomon.reversal B = (Tuple.sort (reversalKey B)).symm,
```

where the lexicographic key orders original `B`-block labels decreasingly
and coordinates within each block increasingly. The public
`B.reversePermutation` sends reversed-shape coordinates to original
coordinates:

```text
B.reversePermutation (B.reverse.index i a) = B.index i.rev a.
```

The new `TypeASolomon.reversal_eq_reversePermutation_symm` proves

```text
TypeASolomon.reversal B = B.reversePermutation.symm.
```

It applies `Tuple.eq_sort_iff` to `B.reversePermutation`. Decomposing
two coordinates by `B.reverse.indexEquiv`, monotonicity of
`blockIndex B.reverse` orders their block indices. Distinct block
indices give the required decreasing original block labels through
`Fin.rev_lt_rev`. Equal block indices give the required increasing
internal coordinates through `index_strictMono`. This proves monotonicity
of the composed reversal key. Injectivity of the key and permutation
supplies the tie condition, identifying the sorting permutation; taking
its inverse gives the displayed equality.

Consequently `w.symm = reversal B` if and only if
`w = B.reversePermutation`. The survivor has the precise target
orientation. For `B = (1,2)`, the public permutation has images `(1,2,0)`,
while its inverse has images `(2,0,1)`; these are generally different.

All steps quantify over every natural rank. At rank zero the edge type is
empty and there is one empty shape and one permutation of `Fin 0`.
The existing cut bijection, cardinality identities and sorting
characterization still apply. Both exponents are zero and the unique
summand has value one. No positive-rank premise or exception is used.

## Provenance and dependency boundary

The original source is Anne-Marie Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie
d'un groupe réductif p-adique*, Trans. Amer. Math. Soc. 347 (1995),
2179–2189, equation (1.9) and the fixed-permutation cancellation on
printed pp.2182–2183 (one-based PDF pp.4–5).

Literature ID: `aubert-1995-duality`. Retained PDF SHA-256:
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
The registered retained copy is
[Aubert (1995)](</home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995.pdf>).

After (1.9), Aubert fixes a one-sided-minimal representative and computes
the signed root-subset sum: a free root cancels the coefficient, while
the remaining representative contributes `(-1)^|K|`. The following page
identifies that representative. The public statement's Markdown records
the derived type-A dictionary. The exact actual subgroup equality, its
cut encoding, the explicit block permutation, the extension to arbitrary
permutations and the rank-zero case are derived finite content. This
module proves that content by the implemented cut and permutation
arguments; it does not transcribe a further representation-theoretic
argument from the source.

The only direct project imports are the unchanged public statement and
`Geometric.TypeASolomonCoefficientProof`. Their project closure, including
this new entry, has 25 modules of lower finite block, matrix, permutation,
cut and local-field mathematics. No classification or exhaustion proof
is used, including any excluded analytic segment, special-head,
strong-head, quotient-coverage, tempered-uniqueness, square-integrable or
regular-exhaustion conclusion or proof successor. The public statement
pair and all its transitive imports are unchanged.

This finite identity is an input for later Jacquet compatibility. It
asserts no Jacquet-functor identity, Aubert involution, irreducible-image
theorem or analytic segment classification.
