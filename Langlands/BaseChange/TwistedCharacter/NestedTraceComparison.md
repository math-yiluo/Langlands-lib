# Nested unramified families agree with the flattened family up to a root of unity

Over a `p`-adic field `E` with topological data `T`, let `B` be a block
shape with refinement `S`, and let `δ i j` be irreducible tempered inner
blocks. Flattening `S` gives the shape `B.flatten S`, whose blocks are
indexed through `B.flattenBlockEquiv S`. The family of flattened blocks is
`Parabolic.flattenedSmoothFamily E T B S δ`.

- `flattened_unitary_irreducible_equiv`: at a unitary parameter `z`, the
  flattened normalized product of the blocks twisted by
  `determinantUnramified _ _ (z (g i j))` is irreducible. It is also
  equivalent to the nested representation
  `normalizedParabolicInduced B (B.blockTensor (nestedInnerRep B S g _ z))`.
  Irreducibility comes from `normalizedProduct_unitaryTwist`, since
  tempered blocks are unitarizable. The equivalence composes two maps:
  - the induction-in-stages equivalence
    `Parabolic.flattenedProductInducedEquiv`;
  - in each outer block, the identification of the inner family
    representation with the normalized product of the twisted inner
    blocks (`nonempty_familyInduced_equiv`).
- `nestedTrace_eq_smul_flat`: let `0 < d` and `σ ^ d = 1`, and let the
  inner blocks carry σ-intertwiners `A i j` with `(A i j) ^ d = 1`. Then
  one `c` with `c ^ d = 1` gives, at every parameter `z`, the nested
  family as `c` times `blockFamilyTrace` of the flattened shape, with the
  flattened blocks, intertwiners and slot map. This holds for every
  left-invariant measure `μ` on `GL_n(E)` that is finite on compact sets. The proof applies `nestedTrace_comparison`,
  with the unitary-point hypothesis supplied by
  `flattened_unitary_irreducible_equiv`.

Transitivity of parabolic induction also enters the proof of
Henniart–Lemaire (2011), II.5.12, Lemme 2, p. 113. That lemma concerns
regularity of an element of `𝒢^{*}_0(G(E),σ)` (II.5.7, p. 105): a
ℤ-linear form `Φ` on `𝒢_0(G(E),σ)` with `Φ(Π, λA) = λ Φ(Π, A)`. It is
not a comparison of families. Comparing the nested and flattened families on
the unitary torus is the Library's route, using Bernstein's
irreducibility of unitary products (Bernstein (1984), Corollary 8.2 a),
p. 89). The source does not argue this way.
