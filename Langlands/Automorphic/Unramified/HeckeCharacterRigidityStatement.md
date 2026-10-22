# Unramified rigidity for Hecke characters

Author: Worker 44.

This module states a coherent rank-one global input over the actual
`Langlands.Global.HeckeCharacter K`: continuous complex quasi-characters of
the idele-class quotient of a number field. Each declaration is a definition
returning `Prop`. No theorem proof, automorphic existence assumption, or
class-field-theory assumption is introduced.

## Targets and quantifiers

`HeckeFiniteRamificationStatement` says that every Hecke character is
unramified outside a finite set of finite places. The conclusion uses the
published predicate `IsUnramifiedAt`, meaning triviality on the units of the
actual local valuation ring. It asserts the finite exceptional set's
existence; this is not stored in the character's definition.

`HeckePowerTraceIndependenceStatement` takes a finite family
`χ : Fin r → HeckeCharacter K` of pairwise distinct characters. Fix any finite
set `S` outside which all these characters are unramified. If complex scalars
`c i` satisfy

\[
  \sum_i c_i\,\chi_{i,v}(\varpi)^k=0
\]

for every finite place `v` outside `S`, every local uniformizer `varpi`, and
every positive integer `k`, then every coefficient is zero. The Lean
injectivity hypothesis concerns equality of the actual continuous
characters, not equality of chosen representation records. Neither
unitarity nor finite order is required.

`HeckeEulerProductRigidityStatement` takes two finite character families,
with repetitions allowed, that are unramified outside the same finite set.
If

\[
 \prod_i(1-\chi_{i,v}(\varpi)T)
   =\prod_j(1-\eta_{j,v}(\varpi)T)
\]

in `Polynomial ℂ` for all such places and uniformizers, the families agree
up to a bijection of their indices. The conclusion
`∃ e : Fin r ≃ Fin s, ∀ i, χ i = η (e i)` includes equality of lengths and
all multiplicities. This is a statement about the actual character lists.
It does not identify arbitrary automorphic subquotients.

`HeckeLocalComponentRigidityStatement` says that two characters whose
unramified local components agree outside a finite set are equal as
characters of the whole idele-class group. Equality therefore also implies
equality at exceptional finite and infinite places. This is a global
rigidity conclusion, not part of the definition of weak association.

`HeckeCharacterRigidityStatement` conjoins these four complete targets.
Each target internally quantifies `K : Type u`, its `Field` and
`NumberField` instances, and all its other data. The universe `u` is
arbitrary. Family sizes range over all natural numbers, including zero;
empty sums and products have their ordinary meanings. There is no
finite-dimensionality assumption on an unrelated representation space,
no Galois hypothesis on `K`, and no restriction on the degree of `K`.

## Local normalization

The places and completions are the published
`FinitePlace K` and `FiniteCompletion K v`. In pinned Mathlib the completion
has its actual surjective multiplicative valuation into `ℤᵐ⁰`. Its
uniformizers have value `WithZero.exp (-1 : ℤ)`. The Lean variable
`π : (FiniteCompletion K v)ˣ` is a nonzero local-field element; it is not
required to be a unit of the valuation ring. The displayed valuation
equality expresses additive valuation one.

For an unramified character, the value on a uniformizer is independent
of the uniformizer: the ratio of two uniformizers is an integral unit,
and the character is trivial there. Quantifying over every uniformizer
avoids selecting any representatives. Uniformizers exist in these actual
completions; pinned Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective`
ensures that this formulation is not vacuous.

The polynomial is exactly `1 - χ_v(π) * T`, represented by
`1 - Polynomial.C (χ_v π : ℂ) * Polynomial.X`. It is the reciprocal
Euler-factor polynomial, with constant coefficient one. At the spectral
value `T = q_v^(-s)` its inverse is the usual unramified rank-one
L-factor. No residue cardinality or spectral parameter is needed in
the polynomial equality itself. There is no inversion of the character
and no additional square-root factor in rank one. This module introduces
no reciprocity or Frobenius convention.

## Original sources and derived specialization

André Weil, *Basic Number Theory*, second edition (1973), Chapter VII,
§§3–4, printed pp.114–118, supplies the concrete quasi-character
conventions. Definition 5 and Proposition 7 distinguish quasi-characters
from unitary characters. Proposition 8 and the unramified convention
after Definition 7 on p.117 identify an unramified local character by its
uniformizer value. The last paragraph before equation (4) on p.118 proves
that a continuous character of the actual idele-class quotient has
unramified local components at almost every place. This is precisely the
first target.

Worker 44 read pp.114–119 of the retained original, whose hash was checked.
Literature ID: `weil-1973-basic-number-theory`. SHA256:
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
Retained file:
`C:/Central-Library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`.
Printed page `p` is one-based PDF page `p + 17`.

Jacquet–Shalika, *On Euler Products and the Classification of Automorphic
Forms II* (1981), §4.2, printed pp.806–807, states linear independence
using all positive power traces of distinct cuspidal classes, allowing
nonunitary quasi-character twists. In rank one a Hecke character is the
one-dimensional automorphic representation of `GL₁(A_K) = A_Kˣ` acting
by multiplication by that character; rational left invariance is exactly
triviality on principal ideles. There are no proper parabolic constant-term
conditions in rank one. Its unramified parameter is the scalar
`χ_v(π)`, whose positive-power trace is `χ_v(π)^k`.
Equivalence of these one-dimensional representations is exactly equality
of the characters. This explains the specialization to actual Hecke
characters and the injectivity hypothesis in the second target.

The third target is the rank-one-constituent specialization of the
inducing-data rigidity argument in §4.4, p.809. Algebraically, equality
of the products gives equality of all positive power sums. Grouping
identical characters and applying the second target makes their
multiplicities equal. The last target is the singleton case. These
derived formulations are not claims that the general higher-rank
automorphic constructions or theorems have already been formalized.
Their Lean proofs remain separate obligations.

Worker 44 visually read the original pp.805–809, and rechecked
pp.805–807 for this specialization.
Literature ID: `jacquet-shalika-1981-euler-ii`. SHA256:
`4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
Retained file:
`C:/Central-Library/Jacquet-Shalika--On Euler products and the classification of automorphic forms II--1981.pdf`.
These printed pages are one-based PDF pages 30–34.

Tate, *Number theoretic background* (Corvallis, Part II, 1979),
§3.1.3, printed p.13, gives the unramified rank-one local factor with
the character evaluated on a uniformizer. Worker 44 read that passage
in the retained original. It fixes the normalization of the polynomial
used above.
Literature ID: `tate-1979-number-theoretic-background`. SHA256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Retained file:
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
Printed p.13 is one-based PDF page 22.

## Library dependencies, checking and coverage

The only project import is `Langlands.Global.HeckeCharacter`, including
its companion `Langlands.Global.Adelic`, in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Worker 44 read both published
pairs and verified that the workspace imports are byte-identical. Their
historical accepted submission was
`0e6d30b8-1a28-49a0-988e-84729eb9f351` version 1, with final semantic
receipt `0021c5fc149c4d7186cf6b5f9fa379d8`; the Lean imports use the
published module names above. The source hashes at this Library base are:

- `Adelic.lean`: `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e`.
- `Adelic.md`: `117b848792dbdbd67225466f0c51c312951803134cdc97dfc895d3f58f9b8c53`.
- `HeckeCharacter.lean`: `68525fbd6a536afefdb696f83491c0ddd60d506390cf7dcb9682c7688c3de18f`.
- `HeckeCharacter.md`: `9af1f28dc3858237fecf97b389a0c581433870404b40274bcb7b37f68323c94f`.

The environment is artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`
version 1, Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The additional direct import
`Mathlib.Algebra.Polynomial.Basic` supplies polynomial notation and algebra.
The normalized valuation comes from Mathlib's actual Dedekind-domain
adic completion infrastructure imported by the accepted adelic group.

All five declarations were printed after elaboration and inspected:
the number field and its instances are internally quantified, the
uniformizer and every positive power are universal, and the finite-family
conclusion is an equivalence of the complete index types. The closing
conjunction uses the same arbitrary universe in each component. A
development Lake build and exact declaration inspection succeeded with
zero warnings and errors; inspection reports `statement_returns_prop:
true`. This verifies well-formedness, not the truth of the four targets.
Independent semantic review and Library publication remain required.

This contribution supplies actual global rank-one prerequisites. The
mixed-rank Jacquet–Shalika linear-independence theorem, general cuspidal
and isobaric rigidity, cyclic base change, automorphic induction and
descent still require the separate actual automorphic definitions and
their corresponding statements. Worker 44 retains those obligations.
Worker 35 retains character-existence, CM, Harris weak-induction and
global functional-equation statements. No statement here substitutes
for those remaining parts of the broad task.
