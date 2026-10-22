# Summed Jacquet lengths as a count on subrepresentations

This internal module fixes a finite set `I : Finset (BlockShape n)` of block
shapes and measures an actual representation `ρ` of `GL_n(F)` by

- `jacquetLength T I ρ := ∑ C ∈ I, repLength (T.normalizedJacquet C ρ)`,

the sum, in `ℕ∞`, of the composition lengths of the actual normalized Jacquet
modules along the shapes in `I`. Here `repLength` is the monoid-algebra module
length of `Filtration.RepresentationLength`, and `T.normalizedJacquet C ρ` is
the project's actual normalized Jacquet module, on the coinvariant quotient of
the restriction to the standard parabolic of shape `C`.

## Results on representations

- `normalizedJacquetEquiv T C e`: an actual equivalence `e : ρ.Equiv σ` gives an
  actual equivalence of normalized Jacquet modules, with forward map
  `T.normalizedJacquetMap C e` and inverse `T.normalizedJacquetMap C e.symm`;
  the two inverse laws are checked on the generators `C.jacquetMk ρ v`.
- `jacquetLength_congr`: equivalent representations have equal summed Jacquet
  length.
- `jacquetLength_eq_add_of_exact`: if the middle term `σ` is smooth, `i : ρ → σ`
  is injective, `q : σ → τ` is surjective, and the range of `i` equals the kernel
  of `q`, then `jacquetLength T I σ = jacquetLength T I ρ + jacquetLength T I τ`.
  The proof applies the published exactness `T.normalizedJacquetMap_exact` at
  each shape and then `repLength_eq_add_of_exact`.
- `jacquetLength_eq_zero_of_subsingleton`: a zero carrier has summed Jacquet
  length zero.

## Results on subrepresentations

For an actual representation `π` with carrier `V`:

- `subtypeMap S` is the inclusion of an invariant subspace as an actual
  intertwiner, and `topEquiv π` identifies the full invariant subspace with `π`.
- `stepQuotient S S'` is the actual quotient of `S'.toRepresentation` by the
  part of `S` inside `S'`.
- `count T I S := (jacquetLength T I S.toRepresentation).toNat`, a natural-number
  function on `Subrepresentation π`.
- `count_bot`: the count of `⊥` is zero. `jacquetLength_top`, `count_top`: the
  full subspace has the summed Jacquet length of `π`.
- `jacquetLength_step` (for smooth `π` and `S ≤ S'`): the length of `S'` is the
  length of `S` plus that of `stepQuotient S S'`, from the exact sequence given
  by the inclusion of `S` into `S'` and the quotient map. `S'` is smooth as an
  invariant subspace of the smooth `π` (`isSmooth_of_injective`).
- `jacquetLength_le` (for smooth `π`): every invariant subspace has at most the
  summed Jacquet length of `π`.
- `count_top_eq_ker_add_range` (for smooth `π` of finite summed Jacquet length
  and an actual intertwiner `A : π → π'`): the count of `⊤` is the count of
  `A.ker` plus the count of `A.range`. The exact sequence is the inclusion of the
  kernel followed by the range restriction of `A`.
- `count_strictMono` (for smooth `π` of finite summed Jacquet length): if every
  step quotient `stepQuotient S S'` with `S ≤ S'` and nontrivial carrier has
  summed Jacquet length at least one, then the count is strictly monotone. A
  strict inclusion `S < S'` gives a nonzero step quotient, and finiteness lets
  the `ℕ∞` sum pass to natural numbers.

These are the properties of a natural-number count on invariant subspaces
(zero at `⊥`, strictly monotone, split along kernel and range of an
intertwiner) that the length-two factor-matching argument of the two-block
proof uses.

## Provenance

Internal. Bernstein–Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), §2.16(1), printed pages 449–450, count composition factors of
an induced representation by the lengths of its Jacquet modules along the
associated Levi subgroups; this module packages that count and its additivity
(exactness of the Jacquet functor) for the two-block factor-matching proof.
No statement here is attributed to that source as a separate theorem.

Imported project constructions:

- `Filtration.RepresentationLength`: `repLength` and its additivity and
  invariance.
- `Parabolic.NormalizedJacquetExactnessProof`: `T.normalizedJacquetMap_exact`,
  exactness of the actual normalized Jacquet functor on sequences with smooth
  middle term.

Author: Worker 286.
