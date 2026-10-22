# Algebraic separation of local factors

This module states the concrete polynomial argument used to recover separate
L and epsilon factors from a gamma identity. It is a prerequisite for the
global-to-local comparison, expressed entirely using Mathlib's complex
polynomials and field of rational functions. It does not introduce substitute
types or predicates for representations or local factors.

## Normalized polynomial separation

`Langlands.Global.GammaPolynomialSeparationStatement` quantifies a natural number
`q > 1`, four complex polynomials `P`, `Pdual`, `Q`, `Qdual`, two nonzero
complex constants `a,c`, and two integer exponents `m,k`. Each polynomial
has constant value 1 at zero. For each original/dual pair the statement
requires that

\[
  P(z)\quad\text{and}\quad
  P_{\mathrm{dual}}(q^{-1}z^{-1})
\]

have no common zero for `z ≠ 0`; the same condition is required of `Q`.
The two epsilon expressions are the rational functions `a X^m` and `c X^k`.
The gamma equality is an identity in `RatFunc ℂ`:

\[
 aX^m\,\frac{P(X)}{P_{\mathrm{dual}}(q^{-1}X^{-1})}
 =
 cX^k\,\frac{Q(X)}{Q_{\mathrm{dual}}(q^{-1}X^{-1})}.
\]

The conclusion is `P = Q`, `Pdual = Qdual`, and equality of the two epsilon
monomials. Equality of the normalized polynomials is equivalent to equality
of their reciprocal rational functions, which represent the two L factors.
Equality is asserted as a rational-function identity, without evaluating at
a possible pole. The no-common-root hypotheses range only over nonzero
complex numbers because the integer powers of `X` account for zero and
infinity separately.

In the local-factor application, `X = q^(-s)` and
`L(s) = P(q^(-s))⁻¹`. The dual L factor at `1-s` therefore contributes
`Pdual(q⁻¹ X⁻¹)⁻¹`, giving the displayed quotient in the stated direction.
The letters `Pdual` and `Qdual` label the inputs that will be supplied by
the actual contragredient factor constructions. This algebraic target itself
does not assume or define any representation-theoretic duality theorem.
The parameter `q` may be any natural number greater than one in this algebraic
lemma; downstream local statements must set it to the actual residue-field
cardinality.

## A sufficient root-region condition

`Langlands.Global.ReflectedRootRegionStatement` quantifies `q > 1`, a
positive real number `r`, and two complex polynomials. It states that the
root bounds

\[
  P(z)=0\ \Longrightarrow\ r\leq |z|,
  \qquad
  P_{\mathrm{dual}}(z)=0\ \Longrightarrow\ r^{-1}\leq |z|
\]

imply the no-common-root condition above. Indeed a root of `P` has norm
at least `r`, so its image under `z ↦ q⁻¹z⁻¹` has norm at most
`q⁻¹r⁻¹`, strictly less than `r⁻¹`. This is an elementary derived
reformulation of the pole-region separation used with Henniart's lemma.
The free radius records reciprocal shifts and is not an extra normalization
of a local absolute value.

`Langlands.Global.GammaSeparationStatement` is the conjunction of these
two proposition definitions. Every mathematical variable is quantified inside
the target. There are no project instances, theorem axioms, or assumptions
that either conclusion already holds.

## Original sources and scope

Guy Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*,
Annals of Mathematics (2) 123 (1986), 145-203, Section 4.4, Lemma and its
proof, printed page 159 (PDF page 16), is the primary source.

- Registered source: `henniart-1986-cyclic`.
- Retained file:
  `C:/Central-Library/Henniart--On the Local Langlands Conjecture for GL(n) The Cyclic Case--1986.pdf`.
- SHA256:
  `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`.

Worker 35 read Sections 4.1-4.5, printed pages 157-160 (PDF pages 14-17),
and visually checked page 159. That check distinguishes the reciprocal
L-polynomial from the L function and confirms that the reflected polynomial
uses the contragredient. The proof on page 159 writes the gamma factor
as a nonzero monomial times the original polynomial divided by the reflected
dual polynomial. Nonzero zeros and poles then recover the normalized
polynomials. The first target is this algebraic argument abstracted from its
representation inputs. The second is a derived sufficient condition on
concrete roots; the supplied source does not display that general-radius
formulation as a separate theorem.

Proposition 4.5 on printed page 160 supplies representation-theoretic
conditions that guarantee noncancellation. Henniart 2000, Theorem 2.3 and
its corollary on pages 444-445, uses unitarity on the Weil side and
temperedness on the automorphic side. Those conditions are not asserted
as proved by this module. Connecting actual arithmetic and automorphic
factor constructors to these polynomial inputs, proving the appropriate
pole-region facts, and the global weak-association comparison are separate
obligations of the broader assigned framework.

The contextual 2000 reference is Guy Henniart, *Une preuve simple des
conjectures de Langlands pour GL(n) sur un corps p-adique*, Inventiones
Mathematicae 139 (2000), 439-455, Section 2.3, printed pages 444-445
(PDF pages 6-7). Its registered source is `henniart-2000-simple-proof`,
retained at
`C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`,
SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

## Formal dependencies and validation

There are no project mathematical imports. The direct Mathlib imports are
`Mathlib.Analysis.Complex.Polynomial.Basic` and
`Mathlib.FieldTheory.RatFunc.AsPolynomial`.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 35 authored this pair. It contains only proposition definitions;
proofs are separate obligations. Native compilation and development check
`ce8614dc-fe4c-4753-b01b-3ab54a557230` compiled the module with no errors or
warnings. The inspection reports that the entire conjunction returns `Prop`,
with no free universe parameters or declared project axioms. Its target
fingerprint is
`92aee388ee6bbb1e5a6732c7fe5d42c106286b746e05cfd023e1e4313b23ca6f`.
These are elaboration results, not mathematical acceptance. Independent
semantic review and current publication remain required; no proof acceptance
is claimed.
