# Reciprocals of entire functions

Placement note (Worker 64): the canonical module is `Langlands.LocalFactor.Analytic.ReciprocalEntire`.
It is moved from `Langlands.LocalFactor.ReciprocalEntire` with every public declaration name,
namespace, type and mathematical body retained. The old module remains a thin
compatibility import. Original source references and authorship below are retained.
Worker 20 authored the original construction; Worker 64 authored only this migration.
The [migration record](../Abelian/Definitions.md#structural-migration-record) gives the complete map and checks.


This internal analytic construction represents the reciprocal of an entire
complex function which is not identically zero. It is intended for the actual
archimedean Gamma factors, whose reciprocals are entire.

`ReciprocalEntire` stores the denominator function, a proof of complex
differentiability everywhere, and a witness that the denominator is nonzero
somewhere. These are conditions on an actual analytic function. No local-factor
identities or existence of an arithmetic epsilon system are postulated.

The reciprocal is represented at each center by its punctured germ, using
`Filter.Germ (nhdsWithin z {z}ᶜ) ℂ`. Values assigned at the center by a total
representative are immaterial to this quotient. Numerical evaluation is
available only on `RegularPoint`, the subtype where the denominator is nonzero,
and produces a complex unit.

`IsPole` means that the denominator vanishes. The construction proves that this
is equivalent to the absence of an analytic representative of the reciprocal's
punctured germ. Thus the denominator retains genuine poles. The proof uses the
identity principle to rule out local identically zero behavior, giving a
punctured neighborhood on which the denominator does not vanish. If the
reciprocal had an analytic representative at a zero, multiplication by the
denominator would have limit zero there, while its punctured values equal one.
Uniqueness of limits gives the contradiction.

The module constructs the constant one, multiplication, spectral translation,
and finite list products. The product denominator is not identically zero
because analytic functions on the connected complex plane have no zero
divisors. Multiplication agrees with multiplication of germs. Poles of a product
are exactly the union of its factors' poles, since the numerator is always one
and no cancellation occurs.

This representation is an internal implementation choice, not a definition
attributed verbatim to an original paper. It implements the requirement to retain
meromorphic functions at their poles emphasized in Tate, *Number theoretic
background* (1979), section 3.3.2, printed page 14 (retained PDF page 23).
The actual Gamma-factor constructors and their original formulas are documented
in the consuming [Archimedean/Definitions](../Archimedean/Definitions.md) pair.

Registered original `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
retained at
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
The cited page was visually read.

The module has no project imports. Its proofs use the pinned Mathlib
`Analysis.Complex.CauchyIntegral`, `Analysis.Analytic.IsolatedZeros`,
`Analysis.Meromorphic.Basic`, and `Order.Filter.Germ.Basic` APIs. In particular,
complex differentiability implies analyticity, the analytic identity principle
supplies isolated zeros, and inversion preserves meromorphic germs.
