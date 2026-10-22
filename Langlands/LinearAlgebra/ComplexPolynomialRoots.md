# Polynomial roots of invertible complex endomorphisms

`Langlands.ComplexPolynomialRoots.{u} : Prop` states that for every
finite-dimensional complex vector space `V : Type u`, every invertible
endomorphism `A : Module.End ℂ V`, and every natural number `n` with `0 < n`,
there is a polynomial `p : Polynomial ℂ` such that

\[
  \bigl(p(A)\bigr)^n=A.
\]

The declaration is a proposition definition, not a proof of this assertion.
Its full outer type is `Prop`; the carrier, its `AddCommGroup`, `Module ℂ`,
and `FiniteDimensional ℂ` instances, the endomorphism, its `IsUnit` hypothesis,
and the positive exponent are all quantified inside the proposition.
The universe of the carrier is arbitrary.

## Interpretation and scope

`Module.End ℂ V` is the ordinary ring of complex linear endomorphisms:
multiplication is composition and its unit is the identity map.
`IsUnit A` means that `A` has a two-sided inverse in this ring.
`Polynomial.aeval A p` evaluates `p` in this complex algebra, with scalar
coefficients acting as scalar multiples of the identity. The power in the
conclusion is therefore an iterated composition of `p(A)`.

The witness is explicitly a polynomial in `A`. This ensures that every
endomorphism commuting with `A` also commutes with the chosen root, since it
commutes with scalar endomorphisms, powers of `A`, and their sums. Merely
asserting the existence of some nth root would not retain this property.
No commutation theorem is added by this statement module.

There is no nontriviality or positive-dimension hypothesis on `V`. When `V`
has dimension zero, its endomorphism ring has a single element, so the
asserted equality holds, for example with the zero polynomial. The statement
assumes neither diagonalizability nor semisimplicity, and supplies no Jordan
basis or root witness among its hypotheses. The exponent is any positive
natural number, independently of the dimension of `V`.

## Source and derived formulation

The source is Guy Henniart, *Representations du groupe de Weil d'un corps
local*, L'Enseignement Mathematique (2) **26** (1980), 155–172,
§2.6, printed page 159 (PDF page 6).
Registered source: `henniart-1980-weil-representations`.
Retained original:
`/home/taskhub/central-library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`.
SHA256: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.

Henniart uses an invertible complex matrix `φ^(mn)` and asserts the existence
of `Q ∈ ℂ[T]` with `Q(T)^(mn)` congruent to `T` modulo the minimal polynomial
of that matrix. Evaluation gives a polynomial root that commutes with the
operators commuting with `φ^(mn)`, as required by his argument in §§2.5–2.6.
The source leaves the polynomial construction to the reader.

The present proposition is a derived generalization of that step: it
quantifies over any invertible endomorphism and any positive exponent, and
expresses the evaluated equality directly. It also passes from matrices to
arbitrary finite-dimensional carriers and explicitly includes dimension zero.
These extensions are not presented as a verbatim theorem of the source.
For positive dimension, the usual mathematical justification is that the
minimal polynomial factors into powers of linear factors with nonzero roots.
One can choose a scalar nth root at each such root, construct a truncated
local root to the required multiplicity, and combine the resulting
congruences by polynomial Chinese remainders. Evaluation then gives the
displayed equality. This explains the scope of the derived statement; a
formal proof is a separate contribution.
