# Opposite associated Jacquet filtration from the upper theorem: proof

Author: Worker 264.

`Langlands.glOppositeCuspidalJacquetFiltrationFromUpper.{uF,uV}` proves the
unchanged published proposition
`Langlands.GLOppositeCuspidalJacquetFiltrationFromUpperStatement.{uF,uV}`
from `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement`.
The statement pair and everything it imports are used unchanged.

This is a conditional transfer. The upper associated-filtration theorem
`CuspidalSupport.AssociatedJacquetFiltrationTheorem.{uF,uV} F T n` stays the
explicit premise of the target, and the proof applies it once, to `B`,
`C.reverse` and `ρ`. The geometric-lemma core of that upper theorem is not
proved here. The proof adds no hypothesis. It retains every quantifier of the
target: an arbitrary prime, an actual `PadicField.{uF} p`, supplied
`TopologicalData`, every rank `n` including zero, and smooth complex carriers
in a universe `uV` independent of `uF`. The inducing representation only needs
to be smooth and quasicuspidal. Irreducibility, admissibility, finite length,
semisimplicity, splitting and an opposite filtration are not inputs. The
quasicuspidality conjunct in the upper conclusion is not used.

All auxiliary declarations live in the namespace
`Langlands.OppositeCuspidalJacquetFiltration`. The coarse Levi reversal
declarations are imported unchanged from the shared
[`Geometric.CoarseLeviReversal`](../Geometric/CoarseLeviReversal.md) pair.
The checked axioms of the main theorem are `propext`, `Classical.choice` and
`Quot.sound`.

## Conventions

Write `t = C.reversePermutation`, `q = C.reverseMatrix R`
(definitionally `permutation n R t`), and `I` for the actual induced
representation `CuspidalJacquetMultiplicity.induced T B (Rep.of ρ.representation)`.
The published coordinate convention is
`t (C.reverse.index j a) = C.index j.rev a`. Whole blocks are reversed and
positions inside a block keep their order. The proof never assumes that `t` or
`q` is an involution.

## Levi relabelling

`leviReverseEquiv C : C.Levi R ≃* C.reverse.Levi R` is
`FiniteTensor.reindexGroup _ Fin.revPerm`, so
`leviReverseEquiv C m i = m i.rev` holds by `rfl`. This is `θ` below. It is
the inverse of the map `κ` in the statement's plan.

`reverseMatrix_mul_leviEmbedding` proves

```text
q * C.reverse.leviEmbedding R (θ m) * q⁻¹ = C.leviEmbedding R m.
```

The proof uses unit and matrix extensionality and writes both coordinates as
`C.index i.rev a` and `C.index j.rev b`. Then
`reverseMatrix_conjugate_entry` reduces the left side to the `(i, j)` entry of
the reversed embedding. The published `leviEmbedding_apply_same` lemma
compares diagonal blocks. For `i ≠ j`, both sides vanish by
`leviEmbedding_apply_ne`. The form
`reverse_leviEmbedding_leviReverseEquiv`, which reads
`C.reverse.leviEmbedding (θ m) = q⁻¹ * C.leviEmbedding m * q`, follows by
group rearrangement.

`conjugatesLevi_reverse C` proves `ConjugatesLevi C.reverse C t`: the image of
the reversed embedded Levi under conjugation by `permutation n F t` is the
original embedded Levi. It uses `θ.symm` in one direction and `θ` in the other.
The main proof transfers the given association: if `w` conjugates `B` to `C`,
then `t⁻¹ * w` conjugates `B` to `C.reverse`. This uses the published
`conjugatesLevi_mul` and `conjugatesLevi_inv` from
`MinimalConjugatingCosetsProof`.

## Quotient comparison

`reverseCoinvariantsEquiv C π` is a linear equivalence from the coinvariants
of `π` for the ambient subgroup `C.reverse.unipotentSubgroup R` to the
coinvariants for `C.oppositeUnipotentSubgroup R`. It is the descent of
`π q`, with

```text
[x] ↦ [π q x],        inverse  [y] ↦ [π q⁻¹ y].
```

Both maps are built with `Jacquet.lift`. For `u` in the reversed upper radical,
`q u q⁻¹` lies in the opposite radical by the published
`reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff`. Hence
`[π q (π u x)] = [π (q u q⁻¹) (π q x)] = [π q x]`. The inverse map is
well defined by the same lemma applied to `q⁻¹ u q`. The two composites
reduce to `π q⁻¹ ∘ π q = 1` and `π q ∘ π q⁻¹ = 1` on representatives.

The Library's upper Jacquet module `C.reverse.JacquetModule π` is the
coinvariant quotient of the restriction to the parabolic, taken by the
parabolic's unipotent radical. `oppositeJacquet` instead uses the ambient
opposite subgroup. `reverseJacquetEquiv` bridges the two models: it composes
the published `C.reverse.jacquetModuleEquiv π`, from the parabolic model to
the ambient upper-subgroup coinvariants, with `reverseCoinvariantsEquiv`. On
classes, `reverseJacquetEquiv_mk` gives
`[x] ↦ [π q x]` by `rfl`. This identification is constructed, not assumed
definitional.

## Normalized equivariance

Recall that `oppositeJacquet T C A` is
`(normalizedActionOfModulus A.ρ N̄ M h δ⁻¹).comp leviEquiv`, where
`δ = (T.leviModulus C).comp (C.leviEquiv F.Carrier).symm`.
`oppositeJacquetReverseEquiv T C A` is a `Representation.Equiv` from

```text
(T.normalizedJacquet C.reverse A.ρ).comp θ
```

to `(oppositeJacquet T C A).ρ`. Its underlying linear map is
`reverseJacquetEquiv C A.ρ`. Equivariance is checked on classes with
`Representation.Coinvariants.hom_ext`.

- Left side: by `normalizedJacquet_mk`, `θ m` acts on `[x]` as the scalar
  `(√(T.leviModulus C.reverse (θ m)))⁻¹` times
  `[A.ρ (C.reverse.leviEmbedding (θ m)) x]`.
- Right side: by `normalizedActionOfModulus_mk`, `m` acts on `[A.ρ q x]` as
  `(√((T.leviModulus C m)⁻¹))⁻¹` times
  `[A.ρ (C.leviEmbedding m) (A.ρ q x)]`.

The published `T.leviModulus_reverse` (from `OppositeProductReversalProof`)
gives `T.leviModulus C.reverse (θ m) = (T.leviModulus C m)⁻¹`, so the scalars
agree. The vectors agree because
`q * C.reverse.leviEmbedding (θ m) = C.leviEmbedding m * q`, which follows from
`reverseMatrix_mul_leviEmbedding`. Hence the inverse upper half-modulus of the
reversed upper action becomes the positive upper half-modulus of
`oppositeJacquet`. No comparison with a Haar modulus is used.

## Minimal-index bijection

`minimalReverseEquiv B C` is an equivalence

```text
MinimalConjugatingPermutations B C.reverse ≃ MinimalConjugatingPermutations B C,
v ↦ t * v,        w ↦ t⁻¹ * w.
```

Permutation multiplication is composition, so `t * v` applies `v` first,
taking `B` to `C.reverse`, and then `t`, taking `C.reverse` to `C`.

- Whole-Levi conjugacy: in the forward direction it comes from
  `conjugatesLevi_mul` with `conjugatesLevi_reverse C`. In the inverse
  direction it also uses `conjugatesLevi_inv`.
- Forward minimality: `IsMinimalRepresentative` has two clauses.
  - First clause: inside each `B` block, `v` is increasing, and the images lie
    in one block of `C.reverse` by `blockIndex_eq_iff_of_conjugatesLevi`
    (from `MinimalWeylTransportProof`). `reversePermutation_lt_of_blockIndex_eq`
    shows that `t` preserves order inside one `C.reverse` block, because
    `t (C.reverse.index i a) = C.index i.rev a` and
    `index_strictMono` holds for both shapes.
  - Second clause: inside each target block `C.index j.rev`,
    `(t * v)⁻¹ = v⁻¹ ∘ t⁻¹`, and `t⁻¹` sends it to `C.reverse.index j` in order
    by `reversePermutation_symm_index`. The clause then follows from the
    second clause for `v`.
- Inverse minimality: for the first clause, `apply_index_eq` (from
  `MinimalWeylTransportProof`) writes `w (B.index i a)` inside a single
  target block of `C`. `reversePermutation_symm_index_strictMono` shows that
  `t⁻¹` is increasing on each block of `C`. For the second clause, `t` sends
  `C.reverse.index j a` to `C.index j.rev a`, and the clause follows from the
  second clause for `w`.

The two inverse laws are `inv_mul_cancel_left` and `mul_inv_cancel_left` on the
underlying permutations. No claim is made about arbitrary minimal Weyl
permutations.

## Transport convention

The published `transport B C w hw ρ` is
`ρ.comp (leviConjugation B C w hw).symm`, which is inverse conjugation.
`leviConjugation_symm_leviReverseEquiv` proves

```text
(leviConjugation B C.reverse v hv).symm (θ m)
  = (leviConjugation B C (t * v) h).symm m.
```

After `B.leviEmbedding_injective` and `leviConjugation_symm_embedding`, this
is `v⁻¹ (t⁻¹ m t) v = (t * v)⁻¹ m (t * v)` as matrices, with
`t⁻¹ m t` supplied by `reverse_leviEmbedding_leviReverseEquiv`. Therefore
`transportReverseEquiv` is the identity linear map. It is an equivalence from
`(transport B C.reverse v hv ρ).comp θ` to
`transport B C (t * v) h ρ`.

## Assembly

Apply the premise to `B`, `C.reverse`, `ρ`, quasicuspidality and the transferred
association. This yields `r`, `e : Fin r ≃ MinimalConjugatingPermutations B C.reverse`,
a filtration `s` of the upper normalized Jacquet module of `I` along
`C.reverse`, and graded equivalences
`g i` to `transport B C.reverse (e i) _ ρ`.
Let `E = oppositeJacquetReverseEquiv T C I`. The proof returns:

- the length `r`;
- the enumeration `e.trans (minimalReverseEquiv B C)`, so the `i`-th index is
  `t * (e i)`;
- the filtration `LengthTwo.transport E (s.comp θ)`. This is the upper
  filtration pulled back along `θ` with the published `ObjectRepFiltration.comp`,
  then carried along `E` onto `oppositeJacquet T C I`;
- for each `i`, the graded equivalence obtained by composing:
  1. the inverse of `ObjectRepFiltration.equivTransportGradedEquiv (s.comp θ) E i`;
  2. `ObjectRepFiltration.compGradedEquiv s θ i`;
  3. the pullback of `g i` along `θ`, using the published
     `FiniteTensorFiltration.compCongr` from `Representation.Tensor.ProductFiltration`;
  4. `transportReverseEquiv`.

The published transport constructions in `Filtration.ObjectTransport` and
`Filtration.LengthTwoMatching` do not need simple factors. The resulting
filtration is the target's actual `ObjectRepFiltration`. It runs from zero to
the whole opposite Jacquet representation and has one step per original
minimal whole-Levi conjugating permutation. The proof does not claim that the
factors are simple or that the filtration is a composition series.

## Provenance

This proof is derived. It transports the explicitly assumed upper filtration by
explicit algebraic conjugation and does not transcribe a further source
theorem. The statement Markdown records the directly read originals:

- Bernstein–Zelevinsky 1977, Corollary 2.13(c) and §2.15(3), printed p.449
  (literature ID `bernstein-zelevinsky-1977-induced-i`).
- Silberger 1979, Theorem 5.4.1.1, printed pp.287–288 (literature ID
  `silberger-1979-harmonic-analysis`).
- Silberger 1978, printed p.97 (literature ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`).

That Markdown also records their locators and hashes.

BZ77 Corollary 2.13(c) is the source of the upper filtration, and it appears
here only as the premise. The opposite-quotient normalization with the positive
upper half-modulus is the convention fixed by `oppositeJacquet`. It matches the
class-exponent convention of Silberger 1978 p.97. The reversal-conjugation route,
the explicit modulus identity and the index bijection `v ↦ t * v` are internal
constructions from the Library's `ReverseBlocks`, `BlockModulus`, Jacquet and
Weyl-transport modules. The proof does not assert Silberger's irreducible
admissible cuspidal theorem, multiplicity counts, or Jordan–Hölder
independence. Those results remain downstream, under their own hypotheses.
