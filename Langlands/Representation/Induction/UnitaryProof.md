# Unitarizability of normalized GL induction: proof

Author: Worker 117.

`Langlands.glNormalizedInductionUnitarity` proves the published closed
`Langlands.GLNormalizedInductionUnitarityStatement.{uF,uV}` from
[UnitaryStatement](UnitaryStatement.md). Its exact type is that proposition,
without additional parameters, typeclasses or theorem-valued assumptions.
The field universe `uF` and carrier universe `uV` are independent.
The two public clause theorems are
`glNormalizedParabolicInductionUnitarity` and
`glNormalizedProductInductionUnitarity`.

The theorem covers every prime `p`, every `F : PadicField.{uF} p`, every
supplied `T : F.TopologicalData`, every positive rank and every ordered block
shape. The first clause accepts any smooth actual complex representation
of the product Levi on `Type uV` with an invariant positive form. The second
accepts actual smooth block representations with unitarizable carriers in
`Type (max uF uV)`. Both conclusions use the existing normalized induction
constructions. The proof adds no admissibility, irreducibility, finite
dimension, square-integrability, topology on the input carrier or completion.

## Actual Levi clause

`glNormalizedParabolicInductionUnitarity` applies the published theorem
`glParabolicCompactScalarIntegral` from
[CompactScalarProof](CompactScalarProof.md). It obtains a compact open
subgroup `K`, the factorization `G = P K`, and a Borel Haar probability
measure `μ` on `K`. The theorem supplies integrability and invariance under
every ambient right translation for locally constant complex scalar
functions satisfying full positive block-modulus covariance. The Haar
instance supplies positivity on nonempty open sets.

Choose an invariant positive form `b` for the inducing representation `σ`.
The proof calls the published constructor
`T.normalizedIntegralForm B σ b K.toSubgroup μ hPK hscalarK` from
[NormalizedIntegralForm](NormalizedIntegralForm.md). The resulting form is
an actual `InvariantPositiveForm (T.normalizedParabolicInduced B σ)` with

```text
H(f,h) = ∫ k : K, b.inner (f(k)) (h(k)) ∂μ.
```

That constructor uses the actual positive-half-modulus covariance
`f(q x) = sqrt(δ_B(m(q))) • σ(m(q)) (f(x))` and the action
`(g · f)(x) = f(x g)`. Conjugate linearity on the left, linearity on the
right and invariance of `b` give full-modulus covariance of the scalar
pairing: the positive real square root is fixed by conjugation and its
square is `δ_B`. Evaluation local constancy gives local constancy of the
pairing. The scalar theorem at `g = 1` supplies integrability; at arbitrary
`g` it supplies invariance of `H` under the entire ambient group.

The imported generic constructor `Induction.integralInvariantPositiveForm`
from [CompactIntegralForm](CompactIntegralForm.md) proves the Hermitian and
sesquilinear laws using scalar integration. The real diagonal integral is
nonnegative. If it is zero, its nonnegative integrand vanishes almost
everywhere. Continuity and Haar full support give pointwise vanishing on
`K`; definiteness of `b` gives `f(k) = 0`. The factorization `G = P K` and
covariance then give `f = 0` on `G`. This proves positive definiteness for
every induced vector, using scalar integration alone.

The scalar input is a proved theorem, not an assumption retained by this
module. Its implementation takes `K = GL_n(O_F)`, reuses the actual Iwasawa
factorization, and proves compact-average invariance directly by a double
integral on `G × P`. It identifies Mathlib's parabolic modular character
with the explicit full block modulus, using `glBlockModulusHaar`. In that
reused radical theorem the forward pushforward remains scaled by the
inverse modulus. This route supplies the required full ambient invariance
without constructing a parabolic disintegration or an invariant scalar
measure on `P \ G`. Compactness and probability normalization come from
the scalar theorem; after its conclusions are available, the form adapter
only needs full support, factorization, integrability and invariance.

## Product clause and universes

`glNormalizedProductInductionUnitarity` chooses an invariant positive form
on each block from its unitarizability hypothesis. It applies
`FiniteTensor.invariantPositiveForm` from
[../Tensor/UnitaryProof](../Tensor/UnitaryProof.md), with index universe `0`,
group universe `uF` and carrier universe `max uF uV`. This supplies an actual
invariant positive form on `B.blockTensor (fun i => (σ i).representation)`.
Its positivity and definiteness hold on all finite tensor sums. The
imported proof constructs global cores by binary algebraic tensor inner
products, recursion over `Fin n` and reindexing; its product formula on pure
tensors is not the sole positivity argument. No finite-dimensionality or
completeness assumption is introduced.

`FiniteTensor.isSmooth_external` supplies smoothness of the actual external
tensor from the bundled smoothness of each factor. The proof rewrites using
`normalizedProductInductionFunctor_obj` and `normalizedProductInduced_eq`,
then applies the actual Levi clause at carrier universe `max uF uV`.
The final theorem pairs the two closed clause proofs at the original
independent universes `uF,uV`.

## Provenance

This is a derived assembly of published Library constructions and proofs.
The scalar proof is by Worker 235; the finite-tensor proof is by Worker 725;
the generic integral construction is by Workers 117 and 15; and its actual
normalized specialization is by Worker 117. These inputs are imported by
Lean name. This module does not modify the statement pair or any pair it
imports, and makes no downstream classification assertion.

The original normalized-induction and compact-picture sources are:

- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft 1 May 1995, sections 2.4 (pp. 26–27) and
  3.1 (pp. 32–33, Propositions 3.1.1, 3.1.3 and 3.1.4). Literature ID
  `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
  Retained original:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- S. S. Kudla, *The local Langlands correspondence: the non-archimedean
  case* (1994), section 1.1, printed p. 368 / retained *Motives*, Part II
  PDF p. 378, equations (1.1.3)–(1.1.4) and the following unitarizability
  paragraph. Literature ID `kudla-1994-local-langlands-nonarchimedean`, SHA-256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
  Retained original:
  `/home/taskhub/central-library/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994.pdf`.

The implemented scalar-average argument and algebraic tensor construction
are the derived routes documented in the imported proof modules. The final
assembly does not require an onto identification with a smooth conjugate
dual, or impose a norm on the arbitrary inducing carrier.
