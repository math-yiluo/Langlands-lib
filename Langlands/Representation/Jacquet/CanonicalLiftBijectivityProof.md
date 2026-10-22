# Bijectivity of the actual stable-image Jacquet map

Author: Worker 203, with Worker 99 credited as coauthor: the averaging helper
`map_averageMap_of_forall_eq` reuses the existing proof, now exposed publicly
under this name, in Worker 99's published
`BlockCompressionProof`.

The closing theorem `Langlands.Jacquet.blockStableImageJacquetBijective.{uF,uV}`
proves exactly `Langlands.Jacquet.BlockStableImageJacquetBijectiveClause.{uF,uV}`
from `Langlands.Representation.Jacquet.CanonicalLiftStatement`. The module also
exposes:

- `stableImageJacquetMap_bijective_of_finiteDimensional`, the same bijectivity
  for any smooth representation whose `K`-fixed vectors are finite dimensional;
- `blockCanonicalLift`, a proof of `BlockCanonicalLiftStatement F T B V`. It
  pairs the published `blockPowerKernelJacquet` with the theorem above.

## Scope and conventions

The closing theorem keeps every parameter of the published target: every
prime, every finite p-adic field in an arbitrary universe `uF`, the supplied
topological data `T`, every natural rank `n`, every block shape `B`, and every
complex module `V` in the independent universe `uV`. Its hypotheses are
exactly admissibility, compactness of `K`, the block Iwahori factorization of
`K`, and strict contraction of `a`. Admissibility is used only through its two
components: smoothness, `hAdmissible.1`, and finite dimensionality of the
`K`-fixed vectors, `hAdmissible.2 K`. The supplied topology and its
general-linear topological-group instance are installed explicitly. Rank zero,
empty and one-block shapes, and the zero representation are not excluded.

Put `N = B.unipotentSubgroup F.Carrier`, `M = B.leviSubgroup F.Carrier`,
`g = B.blockScalar F.Carrier a`, `X = V^K` (the existing `fixedVectors`), and
`S = stableImage ρ hρ K hK g ⊆ X`. Write `q = mk ρ N` for the actual quotient
map to the coinvariants `V_N`, and `A` for the unnormalized quotient action
`action ρ N M h_MN` of `B.blockScalarInLevi F.Carrier a`. The map being proved
bijective is the existing

\[
  \texttt{stableImageJacquetMap}\;\rho\;h_\rho\;K\;h_K\;g\;N\;M\;h_{MN}
  : S \to (V_N)^{M\cap K},
\]

which sends `t` to `q t`. Both carriers are the actual existing ones. No
quotient surjectivity, Jacquet admissibility, canonical lift, compatibility,
pairing or duality is assumed.

## Implemented proof

### Averaging helper

The imported `map_averageMap_of_forall_eq` holds for any smooth representation of a
topological group, compact open subgroup `K`, linear map `f` and vector `v`.
If `f(ρ(k)v) = w` for every `k ∈ K`, then `f` takes the value `w` at the
normalized compact average `Compact.averageMap ρ hρ K hK v`. The `K`-orbit of
`v` is finite by `Compact.finite_orbit_of_smooth`. The average is the finite
mean of that orbit by `Compact.orbitMean_eq_finiteMean`. Linearity sends it
to `card⁻¹ • (card • w) = w`.

### Block-scalar lemmas

`blockScalar_mul_eq_of_mem_leviSubgroup` shows that `g` commutes with every
element of the embedded common Levi `M`. Both are images under
`leviEmbedding`, and `blockScalarLevi_commute` gives commutation in the Levi
product.

`exists_blockScalar_pow_iwahoriLower_fixed` shows that for every vector `v`
there is `s` such that `ρ(g^s)v` is fixed by every element of
`B.iwahoriLower F.Carrier K = K ∩ N⁻`. Smoothness gives an open subgroup `U`
fixing `v`. `K ∩ N⁻` is compact: it is the intersection of the compact `K` with
the closed `N⁻`, and `BlockShape.isClosed_oppositeUnipotentSubgroup` proves
`N⁻` closed. The published `uniformCompactBlockContraction` is applied with an
empty upper compact set and the lower compact set `K ∩ N⁻`, with target
neighbourhood `U`. It gives a depth `ε` such that every `ε`-deep strict
block-scalar tuple conjugates `K ∩ N⁻` into `U` by `x ↦ h⁻¹ x h`.
`strictPowersEventuallyDeep` makes the tuple `(a_i^s)` `ε`-deep for some `s`.
The block-scalar homomorphism identifies its block scalar with `g^s`. Then for
`l ∈ K ∩ N⁻`,
`ρ(l)ρ(g^s)v = ρ(g^s)ρ(g^{-s} l g^s)v = ρ(g^s)v`.

### Injectivity

The published `blockPowerKernel_eq_jacquetKernel` identifies `powerKernelSup`
with the kernel of `fixedJacquetMap` on `X`. The published
`powerKernelSup_isCompl_stableImage` proves `powerKernelSup` and `S`
complementary, using finite dimensionality of `X`. A vector of `S` in the
kernel of the stable-image map therefore lies in both complements, so it is
zero.

### Surjectivity

First, every `x ∈ X` has the quotient of some `t ∈ S` (`hsplit`). By
complementarity `x = k + t` with `k ∈ powerKernelSup` and `t ∈ S`, and the
kernel equality gives `q k = 0`.

Second, powers of `A` can be cancelled on `q(S)` (`hstep`, `hpow`). Suppose
`q t = A z` for some `t ∈ S`. The published `stableImageAction_bijective`
writes `t = C t'` with `t' ∈ S`, where `C` is the compressed action of `g`.
The published `blockCompressedAction_mk` gives `q(C t') = A(q t')`. So
`A(q t') = A z`, and `A` is injective because it is the action of a group
element. Hence `q t' = z`. Induction on `s` extends this from `A` to `A^s`.

Third, let `y ∈ (V_N)^{M∩K}`. Choose a representative `v` with `q v = y`, and
choose `s` as in `exists_blockScalar_pow_iwahoriLower_fixed`. Put
`w = ρ(g^s)v`. For `m ∈ M ∩ K` (`hlevi`), commutation of `m` with `g^s` and
the quotient law `action_mk` give `q(ρ(m)w) = A^s(m · y)`. Fixedness of `y`
makes this `A^s y`. For an arbitrary `k ∈ K` (`hconst`), the supplied
factorization `hfac.1.2` writes `k⁻¹ = l m u` with `l ∈ K ∩ N⁻`,
`m ∈ M ∩ K` and `u ∈ K ∩ N`. Thus `k = u⁻¹ m⁻¹ l⁻¹`. The factor `l⁻¹` fixes
`w`; the upper factor `u⁻¹ ∈ N` disappears in the quotient by
`mk_apply_subgroup`; and the Levi factor gives `A^s y`. Hence
`q(ρ(k)w) = A^s y` for every `k ∈ K`. The averaging helper with `f = q` gives
`q(e_K w) = A^s y`, where `e_K w = Compact.averageMap ρ hρ K hK w ∈ X` by
`Compact.averageMap_mem_fixedVectors`. By the first step `q(e_K w) = q t` for
some `t ∈ S`. So `A^s y ∈ q(S)`, and the second step gives `y ∈ q(S)`. The
subtype codomain is handled by `Subtype.ext`.

### Closing theorems

`stableImageJacquetMap_bijective_of_finiteDimensional` combines the two
directions. `blockStableImageJacquetBijective` applies it with
`hAdmissible.1` and `hAdmissible.2 K`. `blockCanonicalLift` forms the
conjunction with the published `blockPowerKernelJacquet`.

## Deviation from the suggested route

The task context proposed first replacing `v` by a representative fixed by
`M ∩ K`, using a finite-orbit mean over `M ∩ K`, and proving invariance of the
range under `A⁻¹` by a finite-dimensional injective-endomorphism argument.
The implementation needs neither step. The Levi factor of each `K`-translate
is handled in the quotient, where the `(M ∩ K)`-fixedness of `y` and the
commutation of `g^s` with `M` already give the value `A^s y`. Inverse
invariance is replaced by the cancellation step, which uses surjectivity of
the compressed action on `S`, the quotient law and injectivity of `A`. No
average over a non-open subgroup, Haar or subgroup-index comparison, or bound
on central scalars is used.

## Provenance

This is a derived proof from published Library theorems. It imports
`Langlands.Representation.Jacquet.BlockPowerKernelProof` (kernel equality and
`blockPowerKernelJacquet`) and
`Langlands.Representation.Jacquet.CompressionStabilizationProof`
(`powerKernelSup_isCompl_stableImage`, `stableImageAction_bijective`).
Through these it uses `Langlands.Representation.Jacquet.BlockCompressionProof`
(`blockCompressedAction_mk`) and `Langlands.Group.GL.BlockContractionProof`
(`uniformCompactBlockContraction`, `strictPowersEventuallyDeep`). The target
pair and every imported existing Library pair are unchanged. Only the axioms
`propext`, `Classical.choice` and `Quot.sound` occur.

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019: Proposition III.5.5 on page 7,
with Lemma III.5.4 on page 6. Registered source:
`casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`. The
implemented argument works directly with the normalized compact average and
the unnormalized quotient action, as described above. It does not transfer
Casselman's coset-sum operator identities through a scalar comparison.
