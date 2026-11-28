# Proper induced twisted traces as combinations of unramified block families

Over a `p`-adic field `E` with topological data `T`, let `σ` be an
automorphism with `σ ^ d = 1` for some `d > 0`, with the supplied
`F`-module topology. This
module shows that every generator of `sigmaProperInducedSpan` is a finite
combination of unramified families of irreducible tempered σ-stable
blocks evaluated at real exponents. The inducing data may be arbitrary,
including non-tempered data. Each family lives on a shape with at least
two blocks.

## The two families of traces

- `blockShape_length_pos` and `length_le_flatten_length`: every shape of
  positive rank has a block, and flattening a refinement does not
  decrease the number of blocks.
- `flatRealFamilySet T hModule σ n μ` is the set of the following
  distributions:

  `blockFamilyTrace T hModule σ L id δ _ A μ (fun k => realPowerParameter T (x k))`

  Here `L` is a shape of `n` with `2 ≤ L.length`, the blocks `δ` are
  irreducible and tempered, `A` are arbitrary σ-intertwiners, and the `x k`
  are real exponents.
- `normalizedFamilySet T hModule σ m d μ` is the same kind of set on
  `GL_m`, with arbitrary shapes and intertwiners satisfying
  `A k ^ d = 1`.

## Expansion

- `twistedDistribution_mem_span_normalizedFamilySet`: the twisted trace of
  a σ-stable irreducible admissible representation of `GL_m(E)`, `m > 0`,
  lies in the span of `normalizedFamilySet`. `stableLanglandsTraceSpan`
  reduces the claim to σ-stable standard traces. Each of these is a block
  family at the real exponents (`standardTrace_eq_standardFamilyTrace`),
  and rescaling its block intertwiners to order dividing `d` changes it by
  a nonzero scalar (`unramifiedFamilyTrace_scale`).
- `transfer_externalFamily_mem`: let `Ttr` be a linear map from Levi
  distributions to distributions on `GL_n` that carries Levi twisted
  traces to normalized induced twisted traces. Take an outer shape `B`
  with at least two blocks, a refinement `C`, irreducible tempered inner
  blocks `δ i j` with σ-intertwiners `A i j` of order dividing `d`, where
  `0 < d` and `σ ^ d = 1`, and real exponents `x i j`. Apply `Ttr` to the
  twisted distribution of the external tensor of the inner families at
  these exponents, with the tensor of their intertwiners. The result lies
  in the span of `flatRealFamilySet`. The proof has three steps.
  1. Index parameters by the blocks of the flattened shape: with
     `e = B.flattenBlockEquiv C`, put
     `z k = realPowerParameter T (x (e.symm k))`. Then
     `external_nestedInner_reparam` rewrites the Levi twisted distribution
     being transferred. Before, it is the distribution of the external
     tensor of the inner families at the real exponents, with the tensor
     of their intertwiners. After, it is the twisted distribution of the
     block tensor of the nested inner representations at `z`, with the
     tensor of the nested inner intertwiners. This is an equality of twisted
     distributions, not of representations.
  2. `Ttr` turns it into `nestedTrace` at `z`.
  3. By `nestedTrace_eq_smul_flat` this is a root of unity times the
     flattened block family, which has at least two blocks.
- `isAdmissible_familyRep_padic` states admissibility of the family
  representation at real exponents.
- `levi_transfer_mem_span`: for a σ-stable irreducible admissible
  representation `Ξ` of a Levi with at least two blocks, the image under
  `Ttr` of its twisted trace lies in the span of `flatRealFamilySet`. The
  proof has three steps.
  1. `Ξ` factors as an external tensor of irreducible admissible blocks
     (`CuspidalSupport.padicLeviAdmissibleFactorization`). Each block is
     σ-stable (`blockFactors_sigmaStable`).
  2. The twisted trace of `Ξ` with its intertwiner is a scalar multiple
     of the twisted trace with the tensor of block intertwiners
     (`exists_twistedDistribution_eq_smul_of_equiv`).
  3. Expand each block's trace in its `normalizedFamilySet`, expand the
     product multilinearly (`twistedDistribution_external_eq_sum`), and
     apply `transfer_externalFamily_mem` term by term.
- `sigmaProperInducedSpan_le_span_flatRealFamilySet`: the proper
  σ-induction span `sigmaProperInducedSpan σ μ` is contained in the span
  of `flatRealFamilySet`. Take a generator: an unnormalized induction from
  a proper standard Levi of an irreducible admissible σ-stable
  representation on any carrier. The proof has three steps.
  1. Lift the carrier to universe `max v w` (`universeLiftRepresentation`
     and `twistedDistribution_inducedSigma_of_equiv`).
  2. Rewrite the unnormalized induction as the normalized induction of the
     inverse half-modulus twist
     (`twistedDistribution_inducedSigma_eq_normalized`).
  3. Apply the Levi transfer `sigmaNormalizedTraceTransfer`, for the
     right-invariant product of Haar measures on the blocks
     (`generalLinear_isMulRightInvariant`), and then
     `levi_transfer_mem_span`.

A similar expansion appears in the proof of Henniart–Lemaire (2011),
II.5.12, Lemme 2, pp. 112–113. That lemma concerns regularity of an
element `Φ` of `𝒢^{*}_0(G(E),σ)`: a ℤ-linear form on `𝒢_0(G(E),σ)` with
`Φ(Π, λA) = λ Φ(Π, A)` (II.5.7, p. 105). Such a form factors through the
quotient `Ḡ(G(E),σ) = 𝒢(G(E),σ) / 𝒢_{0+}(G(E),σ)` (II.5.4, p. 103). In
the proof, a strongly irreducible σ-representation of a Levi `G_α(E)` is
written, modulo `𝒢_{>0}(G_α(E),σ)`, as an integer combination of
standard σ-representations of σ-stable σ-triplets of `G_α(E)`
(Corollaire of II.5.10 on the Levi). Their inducing data are tempered on
smaller Levis `G_β(E)`. Lemme 1 of II.5.12 places the induction of the
`𝒢_{>0}` part in `𝒢_{0+}(G(E),σ)`, where `Φ` vanishes. Transitivity of
parabolic induction then expresses the remaining classes through
inductions of tempered data. In the Lean proof the expansion is
a statement about spans of twisted distributions
(`stableLanglandsTraceSpan`), with no Grothendieck group. The resulting
nested families are then compared with flattened families on the
unitary torus. The source does not make that comparison.
