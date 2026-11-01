# Reversed-dual lower sections and ordinary Jacquet transport

Worker 1197 states the carrier-level transport specified by Worker 484.
The closed proposition `Langlands.RankinSelberg.TwoBlockDualSectionJacquetStatement.{uF,uW}`
is a statement target; this pair supplies no proof of that proposition.

## Original source and derived formulation

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics **105** (1983), 367–464,
registered source `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The relevant passages were visually read: Section 0.4, printed p.376
(one-based PDF p.11); Section 2.1(3)–(4), printed p.386 (PDF p.21);
Section 4.6, printed pp.410–411 (PDF pp.45–46); and Section 4.8 through
(1), printed pp.414–415 (PDF pp.49–50). No source-specific project errata
note was found in the declared notes locations.

Section 0.4 defines the all-ones antidiagonal matrix and inverse transpose,
including the identity matrix in rank one. Section 2.1 realizes coefficients
as `ell(sigma(g)v)` and defines the dual function by left multiplication
by that Weyl matrix followed by inverse transpose. Section 4.6 uses
normalized induction from the lower two-block parabolic and the positive
character of the corner entry of the complementary upper radical.
Section 4.8 reverses the two blocks and compares the corresponding Jacquet
functions at the Weyl–inverse-transpose ambient argument in equation (1).

This proposition is a derived packaging on actual arbitrary block carriers.
Its arbitrary-Levi formula below includes both within-block Weyl factors;
we do not identify that formula with the literal arbitrary-`h_i` display
on printed p.414. No source-error assertion is made. The formula at the
Levi identity is the normalization needed for equation (1).

## Parameters and actual section carriers

Every prime `p` is retained through `Fact p.Prime`, with every
`F : PadicField.{uF} p`, its canonical topology and Borel measurable space.
For arbitrary `t`, `m : Fin 2 → ℕ` and
`h : ∑ i, (m i + 1) = t + 1`, put `a = m 0 + 1`, `b = m 1 + 1`,
`N = t + 1`, and `B = succBlockShape m h`.
Every dependent family `W : Fin 2 → Type uW` of complex modules is allowed,
with block representations `sigma i` of `GL_(m i+1)(F)`. The only
representation-theoretic hypothesis is `∀ i, IsSmooth (sigma i)`.
The universes `uF` and `uW` are independent. Reducible representations,
zero carriers, and either or both blocks of size one are included.

The complete dependent family is reversed:

```
mD i = m i.rev
WD i = W i.rev
sigmaD i = Whittaker.inverseTransposePullback (sigma i.rev).
```

The original additive groups and complex module structures at `i.rev`
are installed explicitly on `WD i`. The reversed rank equality `hD`
is proved by `Equiv.sum_comp Fin.revPerm` followed by `h`.
Both lower inductions use the published `TwoBlockJacquet.Sections` and
`TwoBlockJacquet.inducedRep`, with shapes `succBlockShape m h` and
`succBlockShape mD hD`. Their carriers are the actual normalized covariant
smooth functions, including a uniform open right stabilizer.

## One equivalence and its evaluation laws

Before any character, functional, Haar measure or section is quantified,
the proposition chooses one

```
E : Representation.Equiv
  (Whittaker.inverseTransposePullback
    (TwoBlockJacquet.inducedRep F h sigma))
  (TwoBlockJacquet.inducedRep F hD sigmaD).
```

Thus `E` is a complex linear equivalence on the actual section carriers
and intertwines the pulled-back original ambient action with the target
right translations. Full covariance and uniform smoothness are part of
membership in those carriers; they are not extra premises about a function.

Write `wB i = GeneralLinear.weylLong (m i + 1) F.Carrier`,
`A = B.blockTensor sigma wB`,
`R = PiTensorProduct.reindex ℂ W Fin.revPerm`, and
`T(g) = GeneralLinear.weylLong N F.Carrier * GeneralLinear.inverseTranspose N F.Carrier g`.
The reindexing has codomain `PiTensorProduct ℂ WD` and sends
`⨂ i, v i` to `⨂ i, v i.rev`. For the same `E`, every section and every
ambient element satisfy

```
sectionEval F hD sigmaD (E f) g
  = R (A (sectionEval F h sigma f (T g)))
sectionEval F h sigma (E.symm fD) g
  = A (R.symm (sectionEval F hD sigmaD fD (T g))).
```

There is no extra scalar normalization. In particular the inverse law
uses the inverse of this same tensor reindexing and the original block
Weyl action.

## Scalar realization with the supplied functionals

For every unitary additive character `psi` and every family
`ell i : Whittaker.glInverseFunctionals psi (m i) (sigma i)`, set

```
psiD = psi.scale (-1)
ellD i = RankinSelberg.secondDualFunctional psi (sigma i.rev) (ell i.rev).
```

Zero functionals are allowed. These are the existing Weyl-translated
functionals on the reversed inverse-transpose representations, with
inverse standard character for `psiD`. At every ambient `g` and every
reversed Levi tuple `z`, the same `E` satisfies

```
scalarSection (fun i => (ellD i).val) (E f) g z
  = scalarSection (fun i => (ell i).val) f (T g)
      (fun i => wB i * inverseTranspose (m i+1) F.Carrier (z i.rev) * wB i).
```

In the Lean formula, `z i.rev` initially has rank `m i.rev.rev + 1`.
It is transported to rank `m i + 1` by `GeneralLinear.reindex` along
`finCongr (congrArg (fun k => m k + 1) (Fin.rev_rev i))` before applying
inverse transpose. This is the canonical entry-preserving transport along
the equality of ranks in the displayed formula.

The leading Weyl action in `secondDualFunctional` and the Weyl action on
the section's block vector cancel at `z = 1`, since each Weyl matrix
squares to the identity. The proposition explicitly retains this
specialization: the two scalar sections at `(g,1)` and `(T(g),1)` are
equal with factor one. At arbitrary `z` the two Weyl factors remain.

## Product measures, integrability, and ordinary integrals

For every supplied `nu : AdditiveHaarMeasure F.Carrier`, let
`mu = rectangularMeasure nu a b` and `muD = rectangularMeasure nu b a`.
These are the existing iterated finite product measures of the same
supplied additive Haar measure. No self-duality or integral-points
normalization is assumed.

The statement defines an actual equivalence of rectangle coordinates by

```
rho(X)(i,j) = -X(j.rev,i.rev).
```

Its inverse has the same negative reversed-transpose formula with the
rectangle dimensions exchanged. Both inverse identities are proved in
the local definition using double negation and `Fin.rev_rev`.
The proposition requires `MeasurePreserving rho muD mu` and
`MeasurePreserving rho.symm mu muD`.

For the same `E`, and every `f`, `g` and reversed rectangle `X`, the
published raw integrands satisfy

```
integrand psiD (fun i => (ellD i).val) (E f) g X
  = integrand psi (fun i => (ell i).val) f (T g) (rho X).
```

It also requires both genuine integrability statements

```
IsAbsIntegrableAt psiD (fun i => (ellD i).val) muD (E f) g
  ↔ IsAbsIntegrableAt psi (fun i => (ell i).val) mu f (T g)
IsAbsIntegrable psiD (fun i => (ellD i).val) muD (E f)
  ↔ IsAbsIntegrable psi (fun i => (ell i).val) mu f.
```

These predicates are the published Mathlib `Integrable` predicates for
the actual complex integrands, pointwise and at all ambient elements.
Finally the actual ordinary Bochner integrals obey

```
jacquetFunction psiD (fun i => (ellD i).val) muD (E f) g
  = jacquetFunction psi (fun i => (ell i).val) mu f (T g).
```

This integral equality is stated for every section. Mathlib's ordinary
Bochner integral is zero when its integrand is not integrable; the
explicit integrability equivalences retain the analytic content.
The proposition asserts no unconditional convergence for untwisted
smooth blocks.

## Provenance of the transport and remaining scope

The intended later proof can compose actual lower-to-reversed-upper
block reversal with inverse-transpose upper-to-lower transport. The
identity `diag(w_a,w_b) * B.reverseMatrix = w_N` and actual lower covariance
produce the displayed section evaluation formulas. The radical
calculation sends the reversed rectangle to its negative transpose
with both coordinate orders reversed. Its corner entry gives exactly
the inverse additive character. Finite coordinate permutation and
negation preserve both supplied product Haar measures, so this change
of variables introduces no determinant density or volume factor.
These are the provenance and proof obligations of the stated derived
normalization, not hypotheses assuming the requested conclusions.

The statement uses the current Library section data, dual functionals
and rectangle measures by Lean name. It does not duplicate the published
pure row Fourier companion. It supplies no proof of the lower-quotient
Fourier comparison, the Section 4.7 finite Laurent identity, the strictly
dominant Section 4.10 argument, factor existence, or two-block gamma/L
multiplicativity. There is no independent test representation in this
unit. Reversal of opposite real twists and later identification of
coefficient models remain assembly obligations. A proof of this exact
proposition is a separate successor after its publication.
