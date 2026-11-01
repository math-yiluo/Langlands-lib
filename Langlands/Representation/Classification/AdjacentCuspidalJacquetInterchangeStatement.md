# Adjacent cuspidal Jacquet interchange under an irreducible commuting pair

Author: Worker 949. Worker 320 split the target, its source leads and its
independence requirements from the analytic segment-classification task.

`Langlands.Classification.AdjacentCuspidalJacquetInterchange.{uF,uV} F T` is a
Prop-valued definition. It states that an actual subquotient occurrence of a
supercuspidal block tensor in a normalized Jacquet module survives the
interchange of two adjacent blocks. This module proves nothing about it.

## Exact scope

Fix any prime `p` with `Fact p.Prime`, any `F : PadicField.{uF} p`, and the
supplied `T : F.TopologicalData`. The field universe `uF` and the carrier
universe `uV` are independent. Put `v = max uF uV`. The definition installs
`T.topology`. All quantified data are as follows.

1. `n : ℕ` is arbitrary, including `0`, and `B : BlockShape n` is a standard
   block shape. Its block sizes are positive.
2. `π : SmoothRep.{0,uF,v} ℂ (GeneralLinear n F.Carrier)` is an actual smooth
   complex representation. The premises are `π.IsIrreducible`,
   `π.IsAdmissible` and `π.HasFiniteLength`. Admissibility is an explicit
   input. Finite length is stated as the objective requires. It is
   mathematically implied by irreducibility, but the statement does not rely
   on that.
3. `A : ∀ i, SupercuspidalRep.{uF,v} (F := F.Carrier) (n := B.size i)` is a
   family of actual objects of the published full subcategory. Each `(A i).obj`
   is therefore irreducible and satisfies `IsSupercuspidal`, which includes
   admissibility. The family may repeat isomorphism classes.
4. Let `X = FiniteTensor.externalSmoothObject (fun i => (A i).obj)`. The
   premise is

   ```text
   SmoothRep.IsSubquotient X ((T.normalizedJacquetFunctor B).obj π)
   ```

   This is the published actual relation: there is an actual subrepresentation
   `S`, an actual subrepresentation of `S`, and an isomorphism from `X` to the
   resulting subquotient.
5. `j : ℕ` and `hj : j + 1 < B.length` select the adjacent labels
   `a = ⟨j, _⟩` and `b = ⟨j + 1, hj⟩` of `Fin B.length`.
6. Two premises concern only the supplied objects `(A a).obj` and `(A b).obj`.
   Write `P(x, y)` for
   `(T.binaryNormalizedProductFunctor (B.size x) (B.size y)).obj ((A x).obj, (A y).obj)`.
   The first premise is `P(a, b).IsIrreducible`. The second is

   ```text
   Nonempty (P(a, b) ≅
     (Derivative.generalLinearRankCast T
        (Nat.add_comm (B.size b) (B.size a))).obj P(b, a))
   ```

   This is an actual isomorphism in the smooth category of
   `GL_(B.size a + B.size b)(F)`, so it consists of invertible equivariant
   linear maps.

With `σ = B.adjacentSwap j hj = Equiv.swap a b`, the conclusion is

```text
SmoothRep.IsSubquotient
  (FiniteTensor.externalSmoothObject (fun i => (A (σ i)).obj))
  ((T.normalizedJacquetFunctor (B.permute σ)).obj π)
```

`BlockShape.permute` sends a new position `i` to its original label `σ i`.
The new block `i` has size `B.size (σ i)`, so positions `j` and `j+1` carry
`A b` and `A a`. Every other position keeps its factor and its size. No
nonlinkage, regularity, distinctness or ordering condition is imposed on the
other factors, and repeated factors are kept. The pair itself may consist of
isomorphic objects whenever the two pair premises hold. The statement does not
assume an embedding of `π` into a full cuspidal product. It does not assume
that `X` is a quotient of the whole Jacquet module. It adds no theorem-valued
premise, such as a classification, exactness, transitivity or extraction
statement.

## Rank transports and definitional identifications

There is exactly one literal rank cast:
`Derivative.generalLinearRankCast T (Nat.add_comm (B.size b) (B.size a))`.
It is the published functor from smooth representations of
`GL_(B.size b + B.size a)(F)` to those of `GL_(B.size a + B.size b)(F)`.
It is defined as `Eq.rec` of the identity functor along the given equality,
and its published `generalLinearRankCast_obj` describes it on objects as the
`cast` along that equality. The published
`Classification.BinaryProductBridge.rankCastEquiv` (module
`Classification.TwoSupercuspidalBinaryProductBridge`) identifies it with
composition by the entry-preserving matrix reindexing `reindex (finCongr _)`.
It is applied only to the swapped binary product.

All other identifications are definitional and need no cast. By the published
definitions, `(B.permute σ).length` is `B.length` and `(B.permute σ).size i` is
`B.size (σ i)`. So the family `fun i => (A (σ i)).obj` lies over the Levi group
`(B.permute σ).Levi F.Carrier`, which is
`∀ i : Fin B.length, GeneralLinear (B.size (σ i)) F.Carrier`. The external
tensor of `v`-small factors indexed by `Fin _` has carrier universe
`max 0 0 v = v`. The binary normalized product of `v`-small inputs has carrier
universe `max uF v = v`. The Lean file elaborates with these universe levels.

## Conventions

`T.normalizedJacquetFunctor B` is the published normalized Jacquet module
along the standard upper block parabolic `B.parabolic`. It takes the actual
coinvariants of the block unipotent radical. A Levi element `m` acts by
`(T.leviHalfModulus B m)⁻¹` times the induced quotient action of
`B.leviEmbedding m`. The binary product is the published
`binaryNormalizedProductFunctor`. Block sizes are positive, so by its published
case split both `P(a, b)` and `P(b, a)` fall in the positive-rank branch. That
branch is normalized induction from the upper block parabolic of
`BlockShape.binary`, with positive half-modulus covariance and right
translation. The tensor `X` is the published external tensor of
`Tensor.Finite`, on which the Levi product group acts factorwise.

## Provenance and comparison with the original proof

This statement is derived. No cited original states it verbatim. It isolates
the local step in the proof of the shuffling lemma, under explicit premises on
the one adjacent pair.

- C. Jantzen, *On supports of induced representations for symplectic and
  odd-orthogonal groups*, Amer. J. Math. 119 (1997), no. 6, pp. 1213–1262.
  Source `jantzen-1997-supports-classical`, SHA256
  `cc705b74e7ae22f82d7c79b2a1ac786a8f939a8db6b9cd02f193c8dc43e9e61b`.
  Lemma 5.4 (shuffling) and its proof are on printed pp. 1225–1226
  (PDF pp. 13–14). Section 10 is on printed pp. 1257–1258 (PDF pp. 45–46).
  Section 2, printed pp. 1215–1217 (PDF pp. 3–5), fixes the conventions. For
  `GL_n(F)` the parabolics are block upper triangular. The relation `≥`
  between representations compares multiplicities in the semisimplification.
- C. Jantzen, *On square-integrable representations of classical p-adic
  groups*, Canad. J. Math. 52 (2000), no. 3, pp. 539–581. Source
  `jantzen-2000-square-integrable-classical-i`, SHA256
  `539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.
  Lemma 2.1.2 (shuffling), printed p. 544 (PDF p. 6), states the `GL_n(F)`
  form of the result and proves it by citing Lemma 5.4 and Section 10 of the
  1997 paper.

The cited passages were read in the retained originals, with rendered pages
for the 1997 formulas. PDF locators are one-based. No source-specific file was
found under the public `notes/errata`. This is not a claim that no errata
exist.

In the 1997 proof, `χ` is a tensor of cuspidal factors
`ν^(α_(i,k)) ψ_i`. The `ψ_i` are pairwise inequivalent irreducible unitary
supercuspidals, and the "key observation" treats one adjacent pair
`ν^(α_i) ψ_i ⊗ ν^(α_j) ψ_j` with `i ≠ j`. The argument starts from that pair
inside the minimal Jacquet module `r_(M',G)(π)`. It then makes two
implications. First, it fuses the two blocks into a Levi `M''`. Here it uses
that the only irreducible representation of `GL_(r_i+r_j)(F)` with
`ν^(α_i) ψ_i ⊗ ν^(α_j) ψ_j` in its Jacquet module is the product
`ν^(α_i) ψ_i × ν^(α_j) ψ_j`. Second, it refines in the swapped order, using
`ν^(α_i) ψ_i × ν^(α_j) ψ_j ≅ ν^(α_j) ψ_j × ν^(α_i) ψ_i`. Both facts come from
the irreducibility of the pair product. The proof recalls that irreducibility
for `i ≠ j`; Zelevinsky's theorem, quoted there as Theorem 2.1, gives it.
Section 10 says that
Lemma 5.4 holds "for the same reasons" when the families are replaced by
`{ν^(β_k+z) ψ_i}_(z ∈ ℤ)` with distinct `β_k`. Jantzen 2000 Lemma 2.1.2
records the `GL_n` version under its conditions (a)–(c).

This statement differs from those sources in the following ways.

- **The pair condition.** The source's conditions on the pair are replaced by
  the two explicit premises the proof actually uses: an irreducible pair
  product, and an actual isomorphism to the swapped product after the rank
  cast. The source derives the isomorphism from irreducibility. Here it is
  assumed for the supplied pair. No unitarity, inequivalence or real-exponent
  normal form is required.
- **The other factors.** The remaining factors are arbitrary irreducible
  supercuspidals in arbitrary order, with repetitions. In the source they are
  the cuspidal `λ_ℓ`.
- **Actual subquotients.** Hypothesis and conclusion use the actual
  subquotient relation, not the source's semisimplified `≥`. The proof
  successor must produce an actual subquotient occurrence. Equality of
  virtual classes or of cuspidal contents is not enough.
- **One transposition.** Only the forward direction of Lemma 5.4(1) is
  claimed, for one adjacent transposition. General shuffles, the converse
  direction and Lemma 5.4(2) about induced representations are not part of
  this statement.

The generalization is still the mechanism of the source proof, run under the
explicit pair premises. The two cited implications and the transitivity of
Jacquet modules under fusing blocks are proof obligations of the successor.
They are not premises here.

## Intended proof route and independence

A proof may fuse labels `j` and `j+1` of `B` into one block. It would use
Jacquet transitivity to obtain an irreducible actual subquotient of the
coarser Jacquet module whose fused coordinate has `A a ⊗ A b` in its own
Jacquet module. It would then identify that coordinate with `P(a, b)` using
cuspidality, Frobenius reciprocity and the irreducibility premise. Next it
would transport along the commutation isomorphism and the rank cast. Finally
it would refine again in the swapped order. The published
`CuspidalSupport.normalizedJacquetSubquotient` (module
`CuspidalSupport.JacquetSubquotientProof`), which carries actual subquotients
through normalized Jacquet functors, may serve there after audit.

The proof must be directly and transitively independent of the parent
`aca8805b-054f-4d56-8045-12db7f623404`. The same holds for multisegment
exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, ordered strong-head
existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, quotient coverage
`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, tempered block uniqueness
`52e97845-36bb-457d-b76f-70753334b88c`, the square-integrable Langlands
classification `1cb45da2-7007-4351-a694-594fb148b8d1`, square-integrable
exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4` and regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`. It covers their conclusions and
their proof successors. It must not use the full disjoint-support
classification of the source as a shortcut. Independently proved lower
geometric-lemma, finite-length, tensor, Jacquet exactness and transitivity,
and cuspidal-support results may be reused after audit. A proposition
definition, literature citation, draft or pending task supplies no proved
input.
