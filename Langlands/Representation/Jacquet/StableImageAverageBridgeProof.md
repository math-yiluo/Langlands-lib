# Geometric averaging bridge for nested compact subgroups: proof

Author: Worker 938. The carried task attributes the geometric route to
Worker 48 and its refinement and the bridge interface to Worker 209. Both
are contributors from the previous project instance; their attribution is
retained here. The two generic averaging helpers used below are imported
under their public Library names, so no code is copied from another module.

The closing theorem `Langlands.Jacquet.blockStableImageAverageBridge.{uF,uV}`
proves exactly `Langlands.Jacquet.BlockStableImageAverageBridgeStatement.{uF,uV} F T B V`
from `Langlands.Representation.Jacquet.StableImageAverageBridgeStatement`.
The two clauses also have their own names:

- `blockStableImage_averageMap_mem_stableImage` (clause (a)): the normalized
  `K0` average of an actual `K1` stable-image vector lies in the actual `K0`
  stable image of the same block scalar;
- `blockStableImage_mk_averageMap_eq` (clause (b)): if the upper Jacquet
  class of that vector is fixed by `K0 ∩ M` under the unnormalized quotient
  action, then the `K0` average has the same class.

The statement pair and every imported existing pair are unchanged.

## Scope

The closing theorem keeps the complete telescope of the published
proposition: the prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData`, every rank `n`, every block shape `B`, and
every complex module `V : Type uV`, with independent universes. Inside it
quantifies over every representation `ρ` with smoothness witness `hρ`, open
subgroups `K1 ≤ K0` with compactness witnesses, the existing
`HasBlockIwahoriFactorization` hypotheses for both subgroups, every strictly
contracting tuple `a`, and every `w` in the actual stable image
`stableImage ρ hρ K1 hK1 A`, where `A = B.blockScalar F.Carrier a`.

It adds no hypotheses. In particular it assumes no admissibility, no finite
dimension of `V`, no positive rank or nonempty shape, no nonzero
representation, no quotient surjectivity, no chosen lift inverse, no
canonical-lift bijectivity and no preservation of an arbitrary quotient
class. The larger-Levi fixedness premise of clause (b) stays explicit. Only
`propext`, `Classical.choice` and `Quot.sound` occur among the axioms.

Notation: `e_K = Compact.averageMap ρ hρ K hK` is the published normalized
finite-orbit average, `C_K = compressedAction ρ hρ K hK A` is the
compression `x ↦ e_K (ρ(A) x)` on `K`-fixed vectors, `N` and `M` are the
upper unipotent radical and the block Levi subgroup, and
`q = Jacquet.mk ρ N` is the quotient map to the coinvariants.

## Imported results

- `map_averageMap_of_forall_eq` (from `BlockCompressionProof`): a linear map
  that sends every vector of the `K`-orbit of `y` to `z` sends `e_K y` to `z`.
- `blockCompressedAction_mul` and `blockCompressedAction_mk` (from
  `BlockCompressionProof`): multiplicativity of compression for weakly
  contracting tuples and the unnormalized quotient law.
- `averageMap_apply_of_mem` and `averageMap_averageMap_of_le` (from
  `StablePairingProof`): `e_K (ρ(k) v) = e_K v` for `k ∈ K`, and
  `e_K ∘ e_L = e_K` when `L ≤ K`.
- `blockScalar_mul_eq_of_mem_leviSubgroup` (from
  `CanonicalLiftBijectivityProof`): `A(b)` commutes with every element of `M`.
- `uniformCompactBlockContraction` and `strictPowersEventuallyDeep` (from
  `BlockContractionProof`), and `isClosed_oppositeUnipotentSubgroup`.

## Helper lemmas in this module

1. `exists_blockScalar_pow_inv_conj_iwahoriLower_mem`. For a compact open
   `K`, an open subgroup `U` and a strictly contracting `a`, there is one `R`
   with `(A^s)⁻¹ l A^s ∈ U` for every `s ≥ R` and every `l ∈ K ∩ N⁻`. The
   set `K ∩ N⁻` is compact, because `K` is compact and the opposite radical
   is closed. The closedness lemma needs the valuative, local-field and
   Hausdorff instances from `T`, which are installed locally. Uniform
   contraction is applied with empty upper set and this lower set, and the
   neighbourhood `U` of the identity gives a depth `ε`. Strict contraction
   gives `R` such that every power `a^s` with `s ≥ R` is `ε`-deep. Finally
   `blockScalar (a^s) = A^s`.
2. `isWeaklyContracting_pow_of_averageBridge`: powers of a weakly
   contracting tuple are weakly contracting, by induction using
   `IsWeaklyContracting.mul`.
3. `blockCompressedAction_pow_apply`: `(C_K)^r x = e_K (ρ(A^r) x)` on
   `K`-fixed vectors. By induction with `blockCompressedAction_mul`,
   `(C_K)^r` is the compression for the tuple `a^r`, and
   `blockScalar (a^r) = A^r`.
4. `exists_iwahori_reversed_factorization`: every `k ∈ K` is `u * m * l`
   with `u ∈ K ∩ N`, `m ∈ K ∩ M` and `l ∈ K ∩ N⁻`. Apply surjectivity of
   the lower-Levi-upper product to `k⁻¹` and invert. Only surjectivity of
   the assumed bijection is used.
5. `blockScalar_pow_apply_fixed_of_conj_mem`: if `g⁻¹ l g` lies in a
   subgroup `U` that fixes `x`, then `ρ(l)` fixes `ρ(g) x`.
6. `averageMap_blockScalar_averageMap_of_lower_fixed`. If `K` factorizes,
   `b` is weakly contracting and `y` is fixed by `K ∩ N⁻`, then
   `e_K (ρ(A(b)) (e_K y)) = e_K (ρ(A(b)) y)`. Apply
   `map_averageMap_of_forall_eq` to the linear map `e_K ∘ ρ(A(b))`. Write a
   given `k ∈ K` as `u m l`. Then
   `A(b) k = (A(b) u A(b)⁻¹) · m · A(b) · l`, because `A(b)` commutes with
   `m`. The factor `l` fixes `y`. The factor `m ∈ K` and the factor
   `A(b) u A(b)⁻¹ ∈ K`, which is the upper containment of the factorization
   hypothesis for weakly contracting `b`, are absorbed by
   `averageMap_apply_of_mem`.
7. `mk_averageMap_eq_of_lower_fixed`. If `K` factorizes, `y` is fixed by
   `K ∩ N⁻` and `q y` is fixed by `K ∩ M` under `Jacquet.action`, then
   `q (e_K y) = q y`. Apply `map_averageMap_of_forall_eq` to `q`. For
   `k = u m l`, the factor `l` fixes `y`. The factor `u ∈ N` acts trivially
   on coinvariants (`mk_apply_subgroup`), and `q (ρ(m) y) = q y` is exactly
   the fixedness premise at `⟨m, hm⟩`.

## Clause (a)

Fix `w` and an exponent `m`. Lemma 1, with `K = K0` and `U = K1`, gives `R`.
Since `w` lies in the `K1` stable image, `w = C_{K1}^(R+m) x` for some
`K1`-fixed `x`. Lemma 3 gives `v = e_{K1}(ρ(A^(R+m)) x)`, where `v` is the
underlying vector of `w`. Put `y = ρ(A^R) x`. By lemmas 1 and 5, `y` is
fixed by `K0 ∩ N⁻`. The candidate preimage under `C_{K0}^m` is the
`K0`-fixed vector `e_{K0} y`. By lemma 3 its image is
`e_{K0}(ρ(A^m)(e_{K0} y))`. Lemma 6, applied to the weakly contracting
tuple `a^m`, rewrites this as `e_{K0}(ρ(A^m) y) = e_{K0}(ρ(A^(R+m)) x)`.
Nested averaging (`averageMap_averageMap_of_le` with `K1 ≤ K0`) shows
`e_{K0} v = e_{K0}(e_{K1}(ρ(A^(R+m)) x)) = e_{K0}(ρ(A^(R+m)) x)`.
Hence `e_{K0} v` lies in the range of `C_{K0}^m` for every `m`, which is
membership in the actual `K0` stable image (`mem_stableImage`).

## Clause (b)

Take `R` from lemma 1 again, and write `w = C_{K1}^R x` with `x` fixed by
`K1`. As in clause (a), `y = ρ(A^R) x` is fixed by `K0 ∩ N⁻`, and
`v = e_{K1} y` by lemma 3. The published quotient law
`blockCompressedAction_mk` for the weakly contracting tuple `a^R`,
together with `action_mk`, gives `q v = q (ρ(A^R) x) = q y`. Hence the
premise says that `q y` is fixed by `K0 ∩ M`. Nested averaging gives
`e_{K0} v = e_{K0} y`, and lemma 7 gives `q (e_{K0} y) = q y = q v`.

## Closing theorem

`blockStableImageAverageBridge` introduces the full telescope and the
statement's `let` bindings. It returns the pair of clause (a) and the
implication of clause (b), with the same universally quantified data.

## Provenance and source motivation

This is an internal derivation from published Library objects: the compact
finite-orbit average, compression, the stable image, the block Iwahori
factorization predicate, uniform block contraction, and the coinvariant
quotient. The route is the one recorded in the task context, as described
above.

Motivation: Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter III, *Induced representations and the Jacquet
module*, revision April 29, 2019, Lemma III.5.7 on page 7. Registered
source `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The bridge is a stronger statement for arbitrary smooth complex
representations and is not a literal theorem of that source. The proof
uses normalized finite-orbit averages directly. It does not use
Casselman's unnormalized coset-sum operators, Haar measures, subgroup
indices, admissibility or stabilization of the compression powers.
