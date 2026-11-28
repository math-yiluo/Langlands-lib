# Comparing induced twisted traces with σ-stable standard traces

Over a `p`-adic field `E` with topological data `T` and an automorphism `σ`
with the supplied `F`-module topology, this module compares unramified
families of σ-stable tempered blocks with each other and with σ-stable
standard traces. All traces use a left-invariant measure finite on compact
sets.

- `nonempty_normalizedProduct_twist_equiv_of_matching`: two shapes matched
  by an order isomorphism, with equal sizes and isomorphic blocks, give
  equivalent normalized products after the same unramified twists. An
  order isomorphism of `Fin` types is the identity, so the shapes agree.
- The fact that `σ ^ d = 1` gives `(entrywiseAut σ m) ^ d = 1` is the
  Library lemma `entrywiseAut_pow_eq_one` of
  `Langlands.BaseChange.TwistedCharacter.SemidirectReduction`, which this
  module imports.
- `blockFamilyTrace T hModule σ B g δ hδ A μ` is `unramifiedFamilyTrace`
  of the blocks `δ` with intertwiners `A`, normalized by the half modulus
  `T.leviHalfModulus B`. `blockFamilyTrace_reindex` moves the slot map `g`
  into the parameters.
- `blockFamilyTrace_comparison`: take two families of irreducible tempered
  σ-stable blocks with arbitrary intertwiners, and `0 < d` with
  `σ ^ d = 1`. Suppose
  that at every unitary parameter their normalized products are
  equivalent. Then one nonzero scalar `c` relates their block families at
  every parameter. The proof has three steps.
  1. Rescale each block intertwiner to order dividing `d`
     (`exists_twistingEquiv_normalizingScalar`).
  2. Obtain irreducibility at unitary points from
     `normalizedProduct_unitaryTwist`, since tempered blocks are
     unitarizable.
  3. Apply `unramifiedFamilyTrace_comparison`, then undo the rescaling
     with `unramifiedFamilyTrace_scale`.
- `standardTrace_eq_smul_of_head`: let `n > 0`, `0 < d` and `σ ^ d = 1`,
  and let two ordered tempered Langlands data on `GL_n` have Langlands
  heads `π` and `π'` that are isomorphic. Then their
  σ-stable standard twisted traces are proportional by a nonzero scalar,
  for any block intertwiners. `glRegularLanglandsDataUniqueness` matches
  the two data by an order isomorphism with equal exponents and
  isomorphic blocks. Both standard traces are values of block families at
  the real exponents (`standardTrace_eq_standardFamilyTrace`), and
  `blockFamilyTrace_comparison` compares the families.
- `exists_standardTrace_eq_smul_blockFamilyTrace`: let `n > 0`, `0 < d`
  and `σ ^ d = 1`, and take irreducible tempered σ-stable blocks on a shape
  `L` of `n`, with arbitrary intertwiners `A`, and real exponents `x`.
  Group equal
  exponents with `exists_groupedTemperedDatum`. This gives a datum `t`,
  block intertwiners and a grouping map `q` with `x k = t.exponent (q k)`,
  and the unitary-point equivalences are kept. The block family of `L` at
  `realPowerParameter T (x k)` is then a nonzero multiple of the
  σ-stable standard trace of `t`.

In Henniart–Lemaire (2011), II.5.9, p. 108, the isomorphism class of an
irreducible σ-representation determines its σ-triplet of Langlands up to
`Σ`-conjugacy, and scaling the operator scales the standard
σ-representation. The two theorems above are the forms of these facts
used here. They are derived from regularity in the unramified parameters
and comparison on the unitary torus.
