# Unitarizability of normalized parabolic induction

Author: Worker 388.

This module states preservation of an invariant positive definite Hermitian
form by the actual normalized upper parabolic induction construction. It
contains three closed `Prop`-valued definitions. It supplies targets for a
subsequent proof; none of these preservation assertions is proved here. All
three are proved in `Langlands.Representation.Induction.UnitaryProof`; see
"Proof status" below.

## Exact targets and scope

`Langlands.GLNormalizedParabolicInductionUnitarityStatement` quantifies over:

- every prime `p`, expressed by `[Fact p.Prime]`;
- every `F : PadicField.{uF} p` and every supplied `T : F.TopologicalData`;
- every natural number `n` with `0 < n` and every ordered positive
  `B : GeneralLinear.BlockShape n`;
- every `V : Type uV` with an additive commutative group and a complex module
  structure, and every actual `σ : Representation ℂ (B.Levi F.Carrier) V`.

Using the field topology `T.topology` and the supplied product Levi topology
`T.leviTopology B`, it asserts

```text
IsSmooth σ → IsUnitarizable σ →
  IsUnitarizable (T.normalizedParabolicInduced B σ).
```

Smoothness means that each vector has an open stabilizer in this actual Levi
group. There is no irreducibility, admissibility, square-integrability,
finite-dimensionality, or assumption about the output. The carrier has no
chosen norm, topology, or completion.

`Langlands.GLNormalizedProductInductionUnitarityStatement` has the same field,
realization, positive rank, and block-shape quantifiers. Its inputs are actual
bundled smooth blocks

```text
σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
  (GeneralLinear (B.size i) F.Carrier).
```

From `∀ i, IsUnitarizable (σ i).representation` it asserts
`IsUnitarizable (((T.normalizedProductInductionFunctor B).obj σ).representation)`.
The factorwise smoothness is part of `SmoothRep`; no additional condition on
the factors or induced representation is introduced.

`Langlands.GLNormalizedInductionUnitarityStatement` is exactly the conjunction
of these two closed propositions, instantiated with the same independent
universe parameters `uF` and `uV`. The Levi clause allows a carrier in
`Type uV`; its induced carrier lies in `Type (max uF uV)`. In the product
clause the block carriers, their finite algebraic tensor product, and the
induced carrier all lie in `Type (max uF uV)`. The mathematical derivation of
the product clause applies Levi preservation at the universe of that tensor
carrier. No resizing or equality between `uF` and `uV` is assumed.

The predicate `IsUnitarizable ρ` is the existence of an actual
`InvariantPositiveForm ρ`. This structure extends `InnerProductSpace.Core ℂ V`
and requires `b.inner (ρ g v) (ρ g w) = b.inner v w`. The form is conjugate
linear in its first variable, linear in its second, positive definite, and
invariant under the given action. This is the algebraic form predicate from
`Unitary/Basic`; it is not a classification or coefficient-growth predicate.

## Construction and normalization

Write `G = GL_n(F)`, `P = B.parabolic F.Carrier`,
`M = B.Levi F.Carrier`, and `m(q) = B.leviProjection F.Carrier q`.
These are the actual upper block parabolic and its actual product Levi.
For `m = (m_i)` the explicit full modulus is

```text
δ_B(m) = ∏_(i<j) |det m_i|_F^(B.size j) / |det m_j|_F^(B.size i).
```

Here the determinant norms are the published residue-normalized norms.
`T.leviHalfModulus B` is the positive real square root of `δ_B`, embedded
in `ℂˣ`, and `T.parabolicHalfModulus B` is its inflation through `m`.
The positive sign is fixed. The covariance and action are

```text
f(q x) = sqrt(δ_B(m(q))) • σ(m(q)) (f(x)),
(g · f)(x) = f(x g).
```

`T.normalizedParabolicInduced B σ` is precisely the published smooth induction
on the covariant functions with an open right stabilizer. The covariance is
`normalizedParabolicInduced_covariant`; the right-translation construction is
in `Induction/Parabolic` and `Induction/Definitions`.

The product functor first constructs `B.blockTensor (fun i => (σ i).representation)`
on `PiTensorProduct ℂ` of the underlying block carriers, and then applies this
normalized parabolic induction. The tensor is `FiniteTensor.external`, with
coordinatewise action on pure tensors. `normalizedProductInductionFunctor_obj` and
`normalizedProductInduced_eq` identify the result with these actual
constructions. This module imports `Induction/BlockFactors` and `Unitary/Basic`
without changing either pair or their imports.

## Original sources and derived provenance

The source tuples are:

1. Literature ID `kudla-1994-local-langlands-nonarchimedean`; Stephen S. Kudla,
   *The local Langlands correspondence: the non-archimedean case* (1994),
   section 1.1, printed page 368, retained *Motives*, Part II PDF page 378,
   equations (1.1.3)--(1.1.4) and the following unitarizability paragraph.
   SHA-256:
   `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
   Retained original:
   `/home/taskhub/central-library/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994.pdf`.
2. Literature ID `casselman-1995-admissible-representations`; W. Casselman,
   *Introduction to the theory of admissible representations of p-adic
   reductive groups*, draft of 1 May 1995, section 3.1, printed/PDF pages
   32--33, especially Propositions 3.1.1, 3.1.3, and 3.1.4; also section 2.4,
   pages 26--27, for the invariant functional, and section 2.1, page 18,
   for the Hermitian-form convention.
   SHA-256:
   `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
   Retained original:
   `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.

Both retained originals were read at the cited locations and their complete
file hashes checked on 25 October 2026. The formula on Kudla's printed page
368 was also checked in the rendered page: equation (1.1.3) uses
`δ_P^(1/2)`, which text extraction does not reliably preserve. No
source-specific errata files were present at the Library base consulted.

Kudla presents the inducing Levi representation as a tensor of smooth block
representations, defines positive-half-modulus covariance and right
translation, and explains that this normalization preserves unitarizability.
The general Levi clause here is a derived formulation extending that tensor
presentation to every smooth representation of the actual Levi.
Casselman section 3.1 starts with an arbitrary smooth representation of `M`,
uses the same positive half, gives restriction to a compact picture
(Proposition 3.1.1), expresses the pairing by integration over a good compact
subgroup (Proposition 3.1.3), and states preservation of unitarity
(Proposition 3.1.4). His convention `L_q f = σ(q)^(-1) δ_P(q)^(-1/2) f`
uses left translation by `q^(-1)` and therefore gives the displayed covariance
with positive exponent.

Casselman section 2.1 describes unitarity by an invariant anisotropic Hermitian
form. The Lean predicate explicitly requires positivity; the compact integral
of a positive form gives precisely that stronger explicit data, as in the
positivity argument of Proposition 3.1.4. For arbitrary nonadmissible smooth
carriers, the proof plan below constructs this form directly. It does not
require an onto identification of the representation with the smooth
contragredient of its conjugate. The finite-tensor construction and the
universe-polymorphic specialization are derived algebraic steps. Accordingly
the contribution has derived provenance, with the two originals supplying
the normalized-induction assertion and compact-picture argument.

## Proof plan written with the statement

The following mathematical proof plan was written with the statement, before
any proof existed. It is not a Lean proof supplied by this module. The
published proofs, described under "Proof status" below, follow a shorter route
for the scalar integration step.

1. **Iwasawa and measure comparison.** For each supplied realization and
   block parabolic, construct a compact open subgroup `K` with `G = P K`,
   identify its topology with the one used by the induction construction,
   and normalize its Haar measure by `vol(K) = 1`. Establish the Haar
   disintegration or the equivalent right-invariant positive functional
   `I_δ` on scalar smooth functions satisfying
   `φ(q x) = δ_B(m(q)) φ(x)`. Show that `I_δ(φ) = ∫_K φ(k) dk`.
   This uses the appropriate Haar normalizations and unimodularity of `GL_n`.
   It requires identification of the explicit determinant product `δ_B`
   with the Haar module of conjugation on the upper unipotent radical.
   `Group/GL/BlockModulus` supplies the explicit character and its half.
   The Haar-module comparison is a separate theorem; it is now proved by
   `Langlands.glBlockModulusHaar` (see "Proof status").
   No invariant scalar measure on `P \ G` is being assumed. The functional
   integrates sections with the displayed modulus covariance.

2. **Scalar compact-picture integration.** Given an invariant positive form
   `b` for `σ`, define

   ```text
   H(f,h) = ∫_K b.inner (f(k)) (h(k)) dk.
   ```

   Each pair of induced functions has a common open right stabilizer. Its
   intersection with compact `K` has finite index, so this scalar integrand
   is locally constant with finite image and the integral is a finite
   weighted sum. This avoids any integration in `V`, any completeness
   assumption, and any finite-dimensionality or admissibility assumption.
   Prove independence of the chosen finite presentation, then Hermitian
   symmetry, conjugate linearity in the first variable and linearity in the
   second, as required by `InnerProductSpace.Core`.

3. **Positivity and definiteness.** The diagonal integrand is real and
   nonnegative. If `f ≠ 0`, Iwasawa decomposition and invertibility of the
   covariance operators show that `f` is nonzero somewhere on `K`.
   Local constancy and full support of Haar measure then give a positive
   diagonal integral. This yields definiteness for every vector of the
   actual induced function module, including arbitrary nonadmissible input.

4. **Invariance under the entire group.** Invariance of `b` and the positive
   half character imply

   ```text
   b.inner (f(q x)) (h(q x))
     = δ_B(m(q)) * b.inner (f(x)) (h(x)).
   ```

   Apply the right invariance of `I_δ` from the first obligation to this
   scalar function to obtain `H(g · f, g · h) = H(f,h)` for every `g ∈ G`.
   Right invariance of Haar measure on `K` alone would only establish the
   assertion for `g ∈ K`; the disintegration/modulus step is needed for
   general `g`. Package the resulting core and invariance law as an
   `InvariantPositiveForm (T.normalizedParabolicInduced B σ)`.

5. **Finite tensor forms and the product clause.** Choose a positive invariant
   form `b_i` on each block. Construct the sesquilinear form on the actual
   algebraic tensor product by

   ```text
   b_tensor(⊗_i v_i, ⊗_i w_i) = ∏_i b_i.inner (v_i) (w_i),
   ```

   and prove it descends through the tensor relations. To prove positivity
   and definiteness on arbitrary finite sums, place the finitely many
   participating vectors in finite-dimensional subspaces, use orthonormal
   bases there, and justify injection of their tensor product into the full
   algebraic tensor. Checking only pure tensors does not suffice.
   The coordinatewise action preserves this form by factorwise invariance
   and extension from pure tensors. Smoothness of this actual external
   tensor is already provided by `FiniteTensor.isSmooth_external` for the
   product topology. Apply Levi preservation at the tensor carrier universe,
   then use the actual product-functor identification above.

The imports of this statement module provide the representations, forms, and
tensor smoothness used in this plan. Neither `Tensor/Finite` nor
`Tensor/FiniteProperties` supplies the invariant positive tensor form needed in
the last step; it is supplied by a separate module, named below.

## Proof status

`Langlands.Representation.Induction.UnitaryProof` proves all three
propositions, each with type exactly the stated proposition and with the
independent universes `uF` and `uV`:

- `Langlands.glNormalizedParabolicInductionUnitarity` proves
  `GLNormalizedParabolicInductionUnitarityStatement.{uF, uV}`;
- `Langlands.glNormalizedProductInductionUnitarity` proves
  `GLNormalizedProductInductionUnitarityStatement.{uF, uV}`;
- `Langlands.glNormalizedInductionUnitarity` proves the conjunction
  `GLNormalizedInductionUnitarityStatement.{uF, uV}`.

None adds a hypothesis. In particular, there is no admissibility,
irreducibility or finite-dimensionality condition. The Levi clause takes `K`,
the Haar probability measure on `K`, the factorization `G = P K` and the scalar
invariance from `Langlands.glParabolicCompactScalarIntegral`
(`Induction/CompactScalarProof`). This replaces steps 1 and 4's appeal to a
disintegration or to `I_δ`. The proof then applies the conditional constructor
`T.normalizedIntegralForm` of `Induction/NormalizedIntegralForm`, which builds
the compact-picture form of steps 2-4 from the input form. The product clause
takes the invariant positive form on the full algebraic tensor product from
`Langlands.FiniteTensor.invariantPositiveForm` (`Tensor/UnitaryProof`) and
smoothness from `FiniteTensor.isSmooth_external`. It applies the Levi clause at
the tensor carrier universe `max uF uV`, after rewriting with the
product-functor identification. The Haar-module comparison of step 1 is proved
separately by `Langlands.glBlockModulusHaar` (`Group/GL/BlockModulusHaarProof`).
The scalar proof uses it to identify the full block modulus with the modular
character of the parabolic.

These theorems prove preservation of unitarizability only. The statements and
the cited source assertions do not by themselves supply any square-integrable
or tempered classification result.
