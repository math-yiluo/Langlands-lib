# Unramified families of normalized inductions of induced blocks

Fix a block shape `B` of `n` and a refinement `S` of `B`: each outer block
`i` carries an inner shape `S i`. The inner blocks are representations
`R i j` of `GL_{(S i).size j}(E)` with σ-intertwiners `A i j`. A slot map
`g i : Fin (S i).length → Fin r` assigns them unramified parameters
`z : Fin r → ℂˣ`. This module builds the nested family: the normalized
induction from `B` of the inner unramified families. It proves that the
nested family is regular in `z` and compares it with a family on a single
shape.

- `innerHalfModulus B S i` is the half modulus of the inner shape `S i`.
- `nestedInnerRep B S g R z i` is the inner representation of
  `GL_{B.size i}(E)`. It is the unnormalized induction of
  `twist (leviUnramified E (S i) (g i) z) (familyInducing (S i) (R i) _)`,
  the representation of `unramifiedFamilyTrace` on the inner shape.
  `nestedInnerIntertwiner` is its induced σ-intertwiner.
- `isAdmissible_normalizedParabolicInduced`: normalized parabolic
  induction preserves admissibility. `isAdmissible_nestedInnerRep` and
  `isAdmissible_nestedRep` apply it to the nested family.
- `nestedTrace σ B S g R A μ hR z` is the twisted trace of
  `normalizedParabolicInduced B (B.blockTensor (nestedInnerRep B S g R z))`.
  Its operator is `normalizedParabolicSigmaIntertwiner` of the tensor of
  the inner intertwiners.
- `nestedTrace_regular`: for `0 < d`, `σ ^ d = 1` and irreducible
  admissible inner blocks (with arbitrary inner intertwiners), every test
  function evaluates the nested family to a Laurent
  polynomial in `z`. The proof has three steps.
  1. `sigmaInducedTest` replaces the test function on `GL_n(E)` by a test
     function `fM` on the Levi `B.Levi E`, for the right-invariant product
     measure `Measure.pi` of Haar measures. Each block measure is right
     invariant by `generalLinear_isMulRightInvariant`.
  2. Multiply by the half modulus (`characterMultiplyTest`,
     `twistedDistribution_twist_eq_comp`), so that the Levi distribution
     is that of the untwisted block tensor. Expand the resulting test
     function as a finite combination of pure tensors
     (`SchwartzBruhat.span_piTensor`).
  3. On each pure tensor, the product formula
     `twistedDistribution_external_piTensor` splits the value into inner
     family values. These are Laurent polynomials by
     `unramifiedFamilyTrace_regular`.
- `nestedIntertwiner_pow`: the nested operator has order dividing `d`
  when the inner intertwiners do and `σ ^ d = 1`.
- `nestedTrace_comparison`: let `0 < d` and `σ ^ d = 1`. Let the inner
  blocks be irreducible and admissible with inner intertwiners of order
  dividing `d`. Let a single-shape family
  `unramifiedFamilyTrace σ C h Q AQ κ _ _ μ _` have irreducible admissible
  blocks and intertwiners of order dividing `d`. Suppose that at every
  unitary parameter its induced representation is irreducible and
  equivalent to the nested representation. Then one `c` with `c ^ d = 1`
  satisfies `nestedTrace … z = c • unramifiedFamilyTrace … z` at every
  parameter `z`. The proof applies `regularTwistedDistributionComparison`
  on the circle torus.
- `external_nestedInner_reparam` is an equality of twisted distributions
  on the product `∏ i GL_{B.size i}(E)`, for the product measure
  `Measure.pi μi`; it asserts no equality of representations. Let `w` be
  inner parameters with `z (g i j) = w i j` (hypothesis `hw`). On the left is the twisted distribution of the
  external tensor product of the inner representations
  `nestedInnerRep B S g R z i`, with the tensor product of the inner
  intertwiners. On the right is the twisted distribution of the external
  tensor product of the inner families on the shapes `S i` with the
  identity slot maps at the parameters `w i`, with the tensor product of
  their induced σ-intertwiners. The proof tests both sides on pure tensors
  (`distribution_ext_piTensor`). By `twistedDistribution_external_piTensor`,
  each side is then a product over `i` of values of
  `unramifiedFamilyTrace` on `S i`, at the parameters `j ↦ z (g i j)` and
  `w i` respectively, and these agree factor by factor.

`nestedTrace_regular` is fixed-test regularity: for one test function
`f`, the value of the family at `f` is a Laurent polynomial in `z`. The
corresponding statement in the literature is Rogawski (1988), Lemma
11.1(a), p. 228. It says that the trace functional of a fixed test
function satisfies the regularity condition (II) of the twisted
Paley–Wiener theorem, because the induced operators act on a fixed space
of `K`-fixed vectors by matrices with polynomial coefficients. The proof
here takes a different route: `sigmaInducedTest`, multiplication of the
Levi test function by the half modulus, and the product formula for
external tensor products.

Henniart–Lemaire (2011), II.5.12, Lemme 2, pp. 112–113, proves a
different statement, about an element `Φ` of `𝒢^{*}_0(G(E),σ)` rather
than a fixed test function. By II.5.7, p. 105, that is the space of
ℤ-linear forms `Φ` on `𝒢_0(G(E),σ)` with `Φ(Π, λA) = λ Φ(Π, A)` for
`λ ∈ ℂ×`. Every such form factors through the quotient
`Ḡ(G(E),σ) = 𝒢(G(E),σ) / 𝒢_{0+}(G(E),σ)` of II.5.4, p. 103. Lemme 2
says: if `Φ` is regular on the unramified twists of the inductions of
tempered strongly irreducible inducing pairs, then it is regular for all
strongly irreducible inducing pairs. The proof expands a pair, modulo
`𝒢_{>0}` of the Levi, in standard σ-representations of σ-stable
σ-triplets (Corollaire of II.5.10 on the Levi). Lemme 1 of II.5.12 sends
the induction of the `𝒢_{>0}` part into `𝒢_{0+}(G(E),σ)`, where `Φ`
vanishes because it factors through `Ḡ(G(E),σ)`. The proof then uses
transitivity of parabolic induction and the algebraic map between the
unramified character tori.
