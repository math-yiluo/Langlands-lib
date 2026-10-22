# Structural identities for determinant Euler factors

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Euler.Statement`.
It is moved from `Langlands.LocalFactor.EulerStatement` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
The [migration record](../Abelian/Definitions.md#structural-migration-record) gives the complete map and checks.


Worker 33 authors these proposition targets. The closing proposition is
`Langlands.LocalFactor.EulerFactorStructureStatement`; no theorem proof is
supplied. It reuses Worker 20's actual `eulerPolynomial`, `rationalFactor`,
`regularFactorValue`, and `spectralFactorValue` constructions.

For an endomorphism `A` of a finite-dimensional vector space, the polynomial
is `det(1-X A)`. Its rational reciprocal is an element of `RatFunc K`.
Scalar values use the existing regular-point subtypes: the denominator is
required to be nonzero. All finite-dimensional carrier universes and the
coefficient-field universe are independently quantified. The spectral
component specializes coefficients to the complex numbers.

## Components and hypotheses

- `EulerExactSequenceStatement` takes a short exact sequence of actual
  vector spaces and compatible endomorphisms. Injectivity, surjectivity,
  equality of image and kernel, and both commuting squares are explicit.
  It asserts polynomial and rational-factor multiplicativity, identifies
  the regular domain, and gives the product of values on that domain.
- `EulerDirectSumStatement` applies the same product formula to the actual
  product endomorphism. It requires no additional exactness hypothesis.
- `EulerScalarAndReciprocalStatement` identifies scalar multiplication of
  the endomorphism with polynomial substitution `X ↦ c X`. For an
  invertible endomorphism and `x ≠ 0`, it gives
  `P_A(x)=(-x)^dim(V) det(A) P_(A⁻¹)(x⁻¹)`. This is a polynomial identity
  evaluated away from zero, not an everywhere-defined rational substitution.
- `EulerUnipotentInvarianceStatement` removes a commuting unipotent factor.
  Unipotence means the actual endomorphism `U-1` is nilpotent. Commutation
  with `A` is required; without it the asserted invariance would be false.
- `EulerTensorEigenbasisStatement` assumes an actual eigenbasis for the
  second tensor factor. It gives `P_(A⊗B)=∏_j P_(β_j A)` and the corresponding
  rational-factor identity. It does not assert this formula for a tensor
  factor without the stated basis.
- `EulerCyclicBlockStatement` gives `P_C(X)=P_A(X^(n+1))` for the cyclic
  operator on `n+1` copies of the carrier. Its action is completely specified:
  each coordinate moves to the next, and the last moves to coordinate zero
  through `A`. Polynomial evaluation and regular values have the same
  substitution. This is the linear-algebra step of finite-extension
  induction, not an unsupported epsilon-induction formula.
- `EulerSpectralTranslationStatement` compares the denominator and the
  regular values after replacing `A` by `q^(-t) A` and `s` by `s+t`.
  The positive real `q` here belongs to a general linear-algebra lemma.
  An arithmetic specialization must use the actual residue cardinality;
  this target does not choose or replace an arithmetic `q`.

The constructor already proves basis invariance and invariance under linear
equivalence. Those results are reused and are not submitted again here.
These statements supply the remaining algebraic ingredients for local factors.
They do not by themselves construct inertia invariants, Weil parameters,
Frobenius lifts, or Weil--Deligne semisimplification.

In particular, the exact-sequence target does **not** say that taking
monodromy-kernel inertia invariants preserves exactness. Applying it to
Weil--Deligne L-factors requires an independently proved exact sequence of
the spaces on which their Frobenius operators act. Direct-sum multiplicativity
has no such issue. Likewise, the commuting-unipotent statement supplies an
ingredient of F-semisimplification invariance; it is not that arithmetic
theorem with its parameter hypotheses omitted.

## Mathematical provenance

This is a derived linear-algebra family, extracted from the determinant
definition in the original sources and retaining the conditions actually
needed by those arguments. It is not a claim that each displayed identity
appears as a numbered theorem in those sources.

Tate, *Number theoretic background* (1979), §3.3.2, printed p.14 / PDF p.23,
defines the reciprocal determinant on inertia invariants. The opening of
§3.3 and the paragraph following §3.3.2, printed p.14 / PDF p.23, discuss
its representation-ring properties and inductivity.
Section 4.1.6, printed pp.20–21 / PDF pp.29–30, defines the Weil--Deligne
factor on monodromy-kernel invariants and explicitly distinguishes its
isomorphism-class behavior from additivity on arbitrary exact sequences.
The original pages were read, including the determinant formulas.

Deligne, *Les constantes des equations fonctionnelles des fonctions L*
(1973), §3.5, internal/PDF pp.28–29, gives the determinant Euler polynomial;
§3.8, internal/PDF pp.30–31, states the short-exact-sequence and induction
properties for Weil representations. Lemma 3.9, internal/PDF p.31, gives
exactly the cyclic determinant identity above; its original formula was
checked visually. The algebraic reason for the
short-exact-sequence formula is block triangularity after choosing a
compatible basis. Direct sums are the block diagonal case. Tensoring with
the supplied eigenbasis decomposes the tensor operator into the displayed
scalar blocks. Scalar substitution and the reciprocal formula follow from
the determinant; removing a commuting unipotent factor follows after
triangularizing over an algebraic closure. The spectral statement uses
the exponential definition `q^(-s)=exp(-s log q)`.

Exact retained sources:

- `tate-1979-number-theoretic-background`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
  `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
  at the locators above.
- `deligne-1973-local-constants`,
  SHA256 `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`,
  `C:/Central-Library/Deligne--Les constantes des equations fonctionnelles des fonctions L--1973.pdf`,
  at the locators above.

## Dependency and validation status

The only project dependency is Worker 20's [`Langlands.LocalFactor.Euler.Definitions`](Definitions.md),
accepted definition artifact `0d2c7ab9-da15-43cf-b878-1cffa68969a4`
version 1. Its current publication was verified at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, including the complete final review
receipt `4ab1b76c841f4a79b04d72113e7586c0` and the effective integrated pair.
Its Lean SHA256 is
`6fde12cbc1ed3f8e6e184468f5edab01cf1e597256f06234e0e6d675f1ba617d`.
Its effective Markdown SHA256 is
`9de51349e57cf40b69f329a136d0fe727d7d70a9cee4768ce11fc463fb042077`.
The construction's Lean source is unchanged from the development dependency;
the published documentation was read and its scope reconciled. This statement
imports that genuine construction and does not reimplement or claim ownership
of it.

The pinned environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Development check `5ddf97c2-ba17-4964-8ff8-dec24c9d2450` succeeded with both
modules compiling without warnings or errors. Inspection confirmed a `Prop`
definition with independent universe parameters `u`, `v`, `w`, `z`, and `t`,
and target fingerprint
`dd0ab470f66a207bf6df629749c49c8249e1a4c78950174bbcb47341ef1f2468`.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the inspected
target assumptions. The checked statement and imported Lean bytes are unchanged,
so the successful exact check remains applicable. This is development validation
of a statement, not independent semantic publication or a proof. The statement
still requires its own independent semantic review and publication.
