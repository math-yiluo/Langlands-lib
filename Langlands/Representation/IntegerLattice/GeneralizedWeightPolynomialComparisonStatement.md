# The particular block polynomials and actual coefficient assembly

Worker 709 prepared this statement; Worker 308 checked the source formulas,
quantifier order and actual constructions for submission under whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2. It imports the published
`Langlands.Representation.IntegerLattice.GeneralizedWeightPolynomial`,
constructed by Worker 709 and Worker 308. The particular polynomial matrices
and coefficient polynomials are unchanged. There is no proof in this file.

## Original and derived provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.III, printed
pp.279–280 / one-based PDF285–286, especially the normalized block factors,
finite binomial products and concluding polynomial-entry argument on PDF286.
Registered identifier `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original was read directly for the construction and is the source for
the present comparison. The exact named polynomial matrices, ordered
scalar-polynomial representation, ambient-finrank cutoff and explicit basis
compatibility are internal derived choices. The comparisons below identify
those particular witnesses with the actual source action and coefficient.

The older-edition supplement `renard-2010-corrections-complements`, PDF18–19,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
corrects the grouping of the whole scalar-times-unipotent factor under its
integer power. The 2026 display already has that grouping. The imported
actual block and product formula follow that convention. No negative integer
coordinate is omitted.

## Inputs and common conventions

Every name below lies in namespace `Langlands`. Each component is a closed
`def` returning `Prop`, universally binding every natural d, every
`V : Type u`, its additive commutative group, complex module and
finite-dimensional structure, and every actual
`A : IntegerLattice.CommutingInvertibleTuple d V`. The carrier universe u
is arbitrary. These comparisons retain the source's finite-dimensional
hypothesis, although the prerequisite's algebraic constructions themselves
have greater internal generality.

Write `W_c = generalizedWeightBlock A c`, `r_c = Module.finrank ℂ W_c`,
and `D = Module.finrank ℂ V`. The polynomial matrix is the actual ordered
product of the scalar-polynomial binomial matrices truncated at D; its
coefficients are the matrix entries of powers of the actual normalized
generator differences. The group element n belongs to the published
`Lattice d = Multiplicative (Fin d → ℤ)`. Polynomial evaluation is always at
`x_n t = (n.toAdd t : ℂ)`. The complex unit character is coerced to ℂ.
The functional ell is an algebraic complex-linear functional, without
conjugation or a topology condition.

## Exact statement components

`CommutingTupleGeneralizedWeightPolynomialActionStatement` asserts, for
every label c, every actual local basis `b : Basis (Fin r_c) ℂ W_c`, every n,
and every row p and column q,

```text
b.repr (generalizedWeightBlockRepresentation A c n (b q)) p
  = (coordinateCharacter c n : ℂ) *
      eval x_n (generalizedWeightPolynomialMatrix A c b p q).
```

No triangularity condition on b is assumed: the finite binomial action
formula is independent of that choice. This restores the scalar character
after evaluation of the explicit polynomial part. It identifies the actual
restricted representation, rather than a supplied polynomial action.

`CommutingTupleGeneralizedWeightPolynomialCoefficientStatement` allows any
supplied family of actual local bases `b c : Basis (Fin r_c) ℂ W_c` and any
actual ambient basis indexed by the full block sigma type,

```text
B : Basis (Σ c : Fin d → ℂˣ, Fin r_c) ℂ V.
```

Its sole additional premise is their exact compatibility,
`∀ c q, B ⟨c,q⟩ = (b c q : V)`. It then chooses one finite set s of labels,
with `c ∈ s ↔ W_c ≠ ⊥`, before every v, ell and n, and asserts

```text
ell (tupleRepresentationEquiv d V A n v)
  = ∑ c ∈ s, (coordinateCharacter c n : ℂ) *
      eval x_n (generalizedWeightCoefficientPolynomial A c (b c) B v ell).
```

The coefficient polynomial is the particular double sum constructed in
the prerequisite: its (p,q) coefficient is
`ell (b c p : V) * B.repr v ⟨c,q⟩`, multiplied by the (p,q) entry of the
polynomial matrix. Thus arbitrary incompatible bases are excluded explicitly.
There is no supplied coefficient identity, spectral support certificate,
replacement action or assumed desired conclusion in the inputs.

`CommutingTupleGeneralizedWeightPolynomialAssemblyStatement` supplies the
actual simultaneous witness existence: for each A it chooses the family b,
ambient basis B and finite set s, with the same compatibility and exact
nonzero-block support, and the same identity for all v, ell and n.
The order of quantifiers means these choices are independent of each
coefficient and lattice point. The preceding compatible-basis component is
stronger as an identity for every compatible pair; the assembly component
also asserts existence of such a pair.

`RenardCIIIPolynomialComparisonStatement.{u}` is exactly the conjunction of
those three closed propositions. It does not assume finite cardinality of
all unit-label tuples or of their full sigma type. Its outer sum uses the
chosen finite support, and each coefficient polynomial uses only its finite
local basis. All ranks, zero spaces and zero blocks are included. In a zero
space exact support forces s to be empty. At d=0 the polynomial matrix is
the empty product identity and the coordinate character is trivial. There is
no nonzero-dimension or positive-rank hypothesis.

## Intended proof route and limits

No proof is provided in this statement file. A future proof should apply
the published all-integer binomial product formula on the actual block,
transport endomorphism addition, multiplication and scalar action through
the actual local basis, and commute scalar polynomial evaluation with the
ordered matrix product. For coefficient assembly, expand v in B, apply the
actual action, group the finitely many coordinates by their exact actual
block support, and use compatibility to apply the local matrix identity.
The published actual decomposition supplies finite support; the published
global block-basis theorem supplies compatible b and B for the existence
component. These are intended steps only, not an implemented proof claim.

The already published existential coefficient theorem uses an alternate
coordinate-induction proof and does not identify these particular polynomial
witnesses. Worker 1214 retains ownership of the separate occurring-character proof
branch. This unit leaves that character proof, every other Appendix C
assertion and all remaining book obligations open. Acceptance of these
statements alone would provide no proof, section completion or publication.
