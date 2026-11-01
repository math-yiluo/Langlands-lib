# Actual reversed-dual lower sections and ordinary Jacquet transport

Worker 1197 proves the existing closed proposition
`Langlands.RankinSelberg.TwoBlockDualSectionJacquetStatement.{uF,uW}` by
`Langlands.RankinSelberg.twoBlockDualSectionJacquet.{uF,uW}`. The target
statement and its imported pairs are unchanged. The auxiliary lemmas in this
module are private components of this proof.

## Original source and normalization

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics **105** (1983), 367–464,
registered source `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The relevant passages were visually read: Section 0.4, printed p.376;
Section 2.1(3)–(4), p.386; Section 4.6, pp.410–411; and Section 4.8
through (1), pp.414–415. In this retained PDF their one-based page
numbers are respectively 11, 21, 45–46 and 49–50. No source-specific
project errata note was found in the declared notes locations.

Section 0.4 fixes the all-ones antidiagonal Weyl matrix, including the
identity in rank one, and inverse transpose. Section 2.1 defines
coefficients by applying a functional to a representation vector and
defines their dual transform at the Weyl–inverse-transpose argument.
Section 4.6 uses normalized induction from the lower two-block parabolic
and integrates over the complementary upper radical with its positive
corner character. Section 4.8 reverses the blocks and obtains the
Jacquet-function identity in (1).

The proved statement is a derived formulation on arbitrary actual block
carriers. Its arbitrary-Levi formula has two within-block Weyl factors.
It is not identified with the literal arbitrary-`h_i` display on p.414,
and no source-error assertion is made. The Weyl factors cancel at the
Levi identity; that factor-one specialization supplies the normalization
used in (1). The proof establishes transport and equivalent convergence
conditions, rather than unconditional convergence for arbitrary smooth
blocks. The original's convergence argument in Section 4.6 is not used
as a premise.

## Actual carriers and one section equivalence

Write `a = m 0 + 1`, `b = m 1 + 1`, `N = t + 1` and
`B = succBlockShape m h`. For every canonical
`F : PadicField.{uF} p`, the block family consists of arbitrary dependent
complex modules `W : Fin 2 → Type uW` and smooth representations
`sigma i` of `GL_(m i+1)(F)`. The field and module universes are
independent. Reducible representations, zero carriers and blocks of
size one are retained.

The complete reversed family is

```text
mD i = m i.rev
WD i = W i.rev
sigmaD i = inverseTransposePullback (sigma i.rev).
```

The additive group and complex module instances on `WD i` are the
original instances at `i.rev`. The reversed rank equality `hD` follows
from `Equiv.sum_comp Fin.revPerm` and `h`.

The private lemma `rawCarrierTransport` composes the published actual
equivalence `Langlands.glOppositeProductReversal` with
`PadicField.TopologicalData.inverseTransposeProductToOppositeEquiv`.
The first map sends original lower induction to reversed upper
induction, reindexes the dependent tensor factors, and evaluates at
`B.reverseMatrix * g`. Its pullback along ambient inverse transpose is
formed using the same linear equivalence and its proved intertwining
law. The second map precomposes by inverse transpose and maps this
upper induction to the lower induction of `sigmaD`. Their composition
is an actual

```text
E : Representation.Equiv
  (inverseTransposePullback (TwoBlockJacquet.inducedRep F h sigma))
  (TwoBlockJacquet.inducedRep F hD sigmaD).
```

These constructors prove covariance and membership in the actual smooth
section carriers in both directions. In block reversal, left
translation and tensor reindexing preserve a section's one uniform
open right stabilizer. In inverse-transpose transport, a uniform open
right stabilizer `K` is replaced by its open comap under the continuous
inverse-transpose automorphism: for all ambient `x` and all `k` in that
comap, `f(θ(x*k)) = f(θ(x)*θ(k)) = f(θ(x))`.
The generic constructors also prove linearity, inverse identities and
ambient intertwining. Composition therefore proves these carrier
obligations without a premise assuming the proposed formula preserves
sections.

Put `wB i = weylLong (m i + 1) F.Carrier`,
`A = B.blockTensor sigma wB`,
`R = PiTensorProduct.reindex ℂ W Fin.revPerm`, and
`T(g) = weylLong N F.Carrier * inverseTranspose N F.Carrier g`.
The entrywise block-index proof `blockWeyl_reverse` shows
`B.leviEmbedding wB * B.reverseMatrix = weylLong N`.
Every `wB i` squares to one. The positive Levi modulus of `wB` also
squares to one, hence equals one. Applying actual lower covariance
therefore contributes no scalar factor. The lemma `carrierTransport`
obtains

```text
sectionEval F hD sigmaD (E f) g
  = R (A (sectionEval F h sigma f (T g)))
sectionEval F h sigma (E.symm fD) g
  = A (R.symm (sectionEval F hD sigmaD fD (T g))).
```

The inverse formula follows from the forward formula using `A² = 1`,
the inverse of the same `R`, and involutivity of `T`. The final theorem
chooses this `E` before quantifying over any character, functional,
Haar measure or section.

## Arbitrary-Levi scalar evaluation

For each supplied unitary additive character `psi` and family
`ell i : glInverseFunctionals psi (m i) (sigma i)`, use exactly

```text
psiD = psi.scale (-1)
ellD i = secondDualFunctional psi (sigma i.rev) (ell i.rev).
```

The underlying linear map of `ellD i` is `ell i.rev` composed with the
action of the corresponding block Weyl matrix. The private lemma
`tensorScalar` proves the required contraction identity by indexed
tensor-product induction. For a scaled pure tensor, it unfolds
`FiniteTensor.external_tprod`, tensor reindexing and tensor
contraction; the two representation compositions become products of
matrices, and commutativity of the two complex factors changes their
order. The addition case uses linearity.

Together with the forward section formula this proves the scalar law
at every reversed Levi tuple `z`:

```text
scalarSection ellD (E f) g z
  = scalarSection ell f (T g)
      (fun i => wB i * inverseTranspose (transport (z i.rev)) * wB i).
```

Here `ell` and `ellD` in this display mean their underlying linear-map
families. In Lean, `transport` is precisely `GeneralLinear.reindex`
along `finCongr (congrArg (fun k => m k + 1) (Fin.rev_rev i))`,
from rank `m i.rev.rev + 1` to `m i + 1`. The proof retains this
canonical rank transport. Specializing to `z = 1`, homomorphisms
preserve one and `wB i * wB i = 1`, so the scalar sections at
`(g,1)` and `(T(g),1)` agree with factor one. No nonzero-functional
assumption is used.

## Supplied product Haar measures

For every supplied additive Haar measure `nu`, let
`mu = rectangularMeasure nu a b` and
`muD = rectangularMeasure nu b a`. Define the actual rectangle
equivalence

```text
rho(X)(i,j) = -X(j.rev,i.rev).
```

Its inverse is the same formula with dimensions exchanged; double
negation and `Fin.rev_rev` prove both inverse identities. Coordinate
evaluation and measurable negation prove measurability in each
direction. Canonical local-field sigma compactness supplies
sigma-finiteness of `nu.measure`; additive Haar invariance under
negation follows from Mathlib's Haar-measure theory.

The private generic helper `measurePreserving_rho` proves preservation
of the exact iterated product measures. It uses
`Measure.pi_eq_generateFrom` on measurable rectangular cylinders.
The cylinder preimage permutes both finite coordinate indices and
negates each coordinate. Negation preserves the supplied Haar
measure; two finite-product reindexings and interchange of the
products give the original cylinder measure. Applying the helper
with dimensions exchanged proves preservation by `rho.symm` as well.
Thus there is no volume or density factor and no self-duality or
integral-points normalization. The cylinder method is adapted from
the Library's elementary
`measurePreserving_transpose_rectangularMeasure` in
`Representation.GodementJacquet.TwoBlockDualParabolicIntegral`;
that module and its analytic consumers are not imported here.

## Integrands, integrability and ordinary Bochner integrals

The private entrywise calculation `radicalConjugate` proves

```text
w_N * inverseTranspose (upperRadical hD X) * w_N
  = upperRadical h (rho X).
```

It splits the two block indices into four cases: the diagonal blocks
are identity matrices, one off-diagonal block is zero, and the other
has entries `-X(j.rev,i.rev)`. Multiplicativity then gives
`T(upperRadical hD X * g) = upperRadical h (rho X) * T(g)`.
At the relevant corner, reversing the indices exchanges zero and the
last index. Hence the positive kernel for `psi.scale (-1)` at `X`
equals the positive kernel for `psi` at `rho X`.
The factor-one scalar law and these two identities prove the raw
integrand equality pointwise for all sections and ambient elements.

The two measurable directions package `rho` as a measurable
equivalence `erho`. The raw identity identifies the reversed
integrand with the original integrand composed with `rho`.
`MeasurePreserving.integrable_comp_emb`, using
`erho.measurableEmbedding`, proves the exact pointwise equivalence
of the published `IsAbsIntegrableAt` predicates, which are actual
Mathlib `Integrable` propositions. It needs no prior measurability
or convergence premise for the integrand. Involutivity of `T`
then proves the equivalence at all ambient elements.

Finally `MeasurePreserving.integral_comp` gives equality of the
ordinary Bochner Jacquet functions. This equality holds for all
sections, including nonintegrable ones under Mathlib's totalized
integral convention. The separately proved `Integrable` equivalences
retain the convergence content; the theorem asserts no unconditional
convergence.

The proof imports only the existing target, actual block-reversal
proof, inverse-transpose induction construction and Mathlib Haar
uniqueness. It does not invoke unrestricted multiplicativity,
dominant or adjacent analytic bases, a lower-quotient Fourier
comparison, a finite Laurent identity or later factor assembly.
