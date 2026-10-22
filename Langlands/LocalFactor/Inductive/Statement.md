# Inductive functions of Weil representations: statements

Worker 33 wrote these proposition definitions for task `e534647a` (row 10 of the
local-factor coverage map). The closing proposition is
`Langlands.LocalFactor.Inductive.InductiveFunctionsStatement`, the conjunction of
the eight statements below. These are statements only: no proof is claimed and
nothing is assumed as an axiom.

All objects come from the companion definition module
`Langlands.LocalFactor.Inductive.Definitions`. Its Markdown explains them:

- the Weil group `W_E` of a p-adic field `E` and Tate's `M(W_E)`, `R(W_E)`, `R⁰(W_E)`;
- `characterClass E χ`, the class of the one-dimensional representation of a
  quasi-character `χ`;
- extensions `E` of `F` (`Extension F`) and towers `E'/E/F` (`IsTower E E' g`);
- induction `Ind_{E'/E}` along the actual Weil map (`induceClass`, `virtualInduce`);
- Tate's additive, inductive and degree-zero-inductive functions
  (`IsAdditive`, `IsInductive`, `IsInductiveInDegreeZero`) with values in an
  additive group `X`.

As in the definitions, `E` is the smaller field of a tower and `E'` the larger.
Tate's `Ind_{E/E'}` is written `Ind_{E'/E}` here.

## The eight statements

### `GallagherDeterminantStatement` (Deligne 1973, Proposition 1.2)

Take any field `K`, any group `G`, a finite-index subgroup `H`, and a
finite-dimensional representation `V` of `H` over `K`. Then

`det(Ind_H^G V) = det(Ind_H^G 1_H)^{dim V} · (det V ∘ t)`,

where `t` is the transfer and `1_H` is the trivial representation on `K`. In Lean:

- `Ind` is the Library's finite-index induction `FiniteRepresentation.induce`;
- `det` is `determinantCharacter`;
- `(det V ∘ t)` is Mathlib's `MonoidHom.transfer` of `det V : H → K^×`.

Deligne writes `ε` for the determinant of the permutation representation of `G`
on `G/H`. This is `det(Ind 1_H)`, so the formula is exactly Deligne's general
form `det(Ind ρ)(x) = ε(x)^{dim ρ} det ρ(t(x))`. Mathlib's transfer agrees with
Tate's transfer on p.3: both are the canonical transfer, independent of the
section. Deligne states the proposition for an arbitrary group and an arbitrary
field `K` (his §1.1), and so does the Lean statement.

### `GenerationStatement` (Tate 2.3.1)

For every p-adic field `E`:

- `R(W_E)` is spanned over `ℤ` by the classes `Ind_{E'/E}[χ]`. Here `E'` runs over
  p-adic fields with an embedding `g : E → E'`, and `χ` over quasi-characters
  (continuous homomorphisms `W_{E'} → ℂ^×`).
- `R⁰(W_E)` is spanned by the classes `Ind_{E'/E}([χ] - [χ'])`.

Tate states this for the base field `F`. The Lean statement quantifies over every
p-adic field `E`, because the base of a tower can be any finite extension. Tate's
proof uses the degree-zero form of Brauer's theorem (Deligne, Proposition 1.5).

### `EulerFactorInductionStatement` (Tate 3.3; Deligne 1973, Proposition 3.8 (ii))

Tate (3.3) says the nonabelian L-function `L(V) = det(1 - Φ | V^I)^{-1}` is
inductive, with `Φ` an inverse (geometric) Frobenius. Deligne proves this as
Proposition 3.8 (ii). The Lean statement takes:

- p-adic fields `E`, `E'` and an embedding `g : E → E'`;
- a continuous representation `V` of `W_{E'}`;
- elements `Φ ∈ W_E` and `Φ' ∈ W_{E'}` of degree one. These are geometric
  Frobenius elements in the Library's degree convention (`localDegreeInt`, the
  convention of `localGeometricFrobenius`).

With `I_E`, `I_{E'}` the actual inertia subgroups (`localInertia`) and `B` the
induced representation `Ind_{E'/E} V` along the Weil map, it asserts:

- `det(1 - X Φ | B^{I_E}) = det(1 - X^f Φ' | V^{I_{E'}})` as polynomials. Here `f` is
  the residue degree of `E'/E` (`extensionResidueDegree`) and the determinant is
  the Library's `LocalFactor.eulerPolynomial` of the action on the actual
  invariant subrepresentation (`invariants`). The right side is
  `Polynomial.expand ℂ f`.
- For every complex `s`, the first polynomial evaluated at `q_E^{-s}` equals the
  second evaluated at `q_{E'}^{-s}`. Here `q` is the actual residue cardinality
  `canonicalTopologicalData.residueCardinality` and `q^{-s} = exp(-s log q)`.
  These are the reciprocal L-factors, so `L_E(Ind V, s) = L_{E'}(V, s)` at every
  point where either side is finite. Evaluating the polynomials avoids assigning
  values at poles.

Both conclusions are independent of the choice of the Frobenius elements. The
second follows from the first together with `q_{E'} = q_E^f`. Deligne's proof
identifies `(Ind V)^{I_E}` with an induced representation of `V^{I_{E'}}` from an
index-`f` subgroup of the unramified quotient. It then uses his Lemma 3.9,
`det(1 - F_n t) = det(1 - F t^n)` for the cyclic block operator. That lemma is
already stated in the Library as `EulerCyclicBlockStatement` (row 3).

### `TraceCharacterTowerStatement`

Tate (3.4.1) uses, for each finite extension `E` of `F`, the additive character
`ψ ∘ Tr_{E/F}` of `E`. Worker 20's `traceCharacter` constructs this character for
the actual trace (`Langlands.HarmonicAnalysis.CharacterTransport`). The statement
asserts that these characters are coherent in towers. For p-adic fields `E`, `E'`,
`E''` with embeddings `g : E → E'` and `h : E' → E''`, and a nontrivial continuous
unitary additive character `ψ` of `E`:

`(ψ ∘ Tr_{E'/E}) ∘ Tr_{E''/E'} = ψ ∘ Tr_{E''/E}`.

All three trace characters use the canonical topologies of the fields. The
algebra structures are those of the embeddings `g`, `h` and `h ∘ g` (the Library's
`extensionAlgebra`). This is transitivity of the field trace. It makes the family
`E ↦ ψ ∘ Tr_{E/F}` in (3.4.1) and (3.4.8) consistent along towers, which a
degree-zero inductivity clause for local constants needs.

### `UniquenessStatement` (Tate 2.3.3)

Let `λ` and `μ` be functions that are inductive in degree zero over `F` with values
in the same group `X`. Suppose they agree on the class of every quasi-character of
`W_E`, for every extension `E` of `F`. Then `λ = μ`. Tate deduces this remark from
2.3.1. A function is first extended to `R(W_E)` by additivity, and
`R(W_E) = R⁰(W_E) + ℤ[1_E]`.

### `DeterminantExampleStatement` (Tate 2.3.4)

Tate fixes `a ∈ F^×` (here `C_F = F^×`) and puts `λ(V) = (det V)(r_E(a))` for
`V ∈ M(W_E)`. Here `r_E : E^× → W_E^{ab}` is the reciprocity isomorphism of
topological groups. On p.3 Tate defines `G^{ab} = G/G^c` for a topological group
`G`, with `G^c` the closure of the commutator subgroup: the maximal abelian
Hausdorff quotient. He states that `λ` is inductive in degree zero, by (W3) and
Gallagher's formula in degree zero.

The Lean statement takes the following data and hypotheses.

- For every extension `E` of `F`, a homomorphism `r_E : E^× → W_E^{ab}` into
  Mathlib's `TopologicalAbelianization (localWeilGroup E)`, the quotient of
  `W_E` by the closure of its commutator subgroup. This is Tate's `W_E^{ab}`.
- Tate's (W3) for every tower `E'/E/F`: `t(r_E(x)) = r_{E'}(g(x))` for all
  `x ∈ E^×`, with `g` the embedding of the tower. The transfer `t` is built from
  Library maps in two steps:
  - `LocalClassField.abelianizedTransfer`
    (`Langlands.ClassFieldTheory.Local.Transfer`) is the continuous transfer
    `W_E^{ab} → H^{ab}` between topological abelianizations. Here `H` is the
    range of the Weil map `W_{E'} → W_E` (`extensionWeilRange`), an open
    subgroup of finite index (`extensionWeilMap_range_isOpen`). The transfer is
    Mathlib's `MonoidHom.transfer`, the canonical transfer that Tate defines on
    p.3 by a section of `H\G`.
  - `LocalClassField.abelianizationMap` then applies the inverse of the
    topological group isomorphism `extensionWeilRangeEquiv : W_{E'} ≃ H` on the
    topological abelianizations.
- A fixed `a ∈ F^×`, mapped into each `E^×` by the embedding of `F`.
- For every extension `E`, an element `w_E ∈ W_E` whose class in `W_E^{ab}`
  (`LocalClassField.abelianizationProjection`) is `r_E(a)`.

The conclusion: `λ_E(V) = (det V)(w_E)` is inductive in degree zero over `F`. Its
values lie in `ℂ^×`, used as `Additive ℂ^×`.

The value does not depend on the choice of the lifts `w_E`. For a continuous
representation `V`, `det V : W_E → ℂ^×` is continuous
(`FiniteRepresentation.continuous_determinantCharacter`,
`Langlands.VirtualRepresentation.ExactDeterminant`). Since `ℂ^×` is abelian and
Hausdorff, its kernel is a closed subgroup that contains the commutators, hence
the closure `W_E^c`. So `det V` factors through `W_E^{ab}`, and
`(det V)(w_E) = (det V)(r_E(a))` in Tate's sense for every lift. Lifts exist
because the quotient map `W_E → W_E^{ab}` is surjective. The statement
quantifies over all lift families. This avoids a separate definition of the
induced character on `W_E^{ab}`.

This is a derived formulation. It assumes only the properties of `r_E` that
Tate's proof uses, namely (W3). Tate's (W3) diagram for `E' ⊂ E` (p.4) says
that the inclusion `C_{E'} → C_E` corresponds to the transfer
`W_{E'}^{ab} → W_E^{ab}`. In the notation here, with `E` smaller, that is the
displayed identity. Here `W_{E'}` is identified with its image in `W_E`. Tate's
reciprocity isomorphisms take values in the same Hausdorff quotients and satisfy
(W3) with the same canonical transfer. So they satisfy the hypothesis, and the
conclusion for them, with any lifts, is Tate's example 2.3.4.

### `DegreeCorrectionStatement`

Let `λ` be inductive in degree zero over `F`, let `E'/E/F` be a tower, and let
`V ∈ M(W_{E'})` have dimension `n`. Then, written additively,

`λ_E(Ind_{E'/E} V) = λ_{E'}(V) + n · (λ_E(Ind_{E'/E} 1_{E'}) - λ_{E'}(1_{E'}))`.

This follows from degree-zero inductivity applied to `[V] - n[1_{E'}]`, which has
degree zero. For local constants, Tate (3.4.8) states only the degree-zero
identity `ε(Ind V_{E'}, ψ) = ε(V_{E'}, ψ ∘ Tr)`. This statement gives the
arbitrary-degree consequence. In multiplicative form the bracket is the constant
usually written `λ(E'/E, ψ)`. Here it is stated for every function that is
inductive in degree zero. It is a derived consequence of Tate (2.3.2), included so
that downstream constant systems can use the correction without re-deriving it.

### `InductiveCharacterizationStatement`

A function is inductive over `F` exactly when it is inductive in degree zero and
`λ_E(Ind_{E'/E} 1_{E'}) = λ_{E'}(1_{E'})` for every tower `E'/E/F`. This is a derived
consequence of (2.3.2) and `R(W_{E'}) = R⁰(W_{E'}) + ℤ[1_{E'}]`. It separates
Tate's two notions by the single correction term.

## Universes

`InductiveFunctionsStatement` has the universe parameters below:

- `u`: the p-adic fields and the representation carriers;
- `v`: the target group `X`;
- `uK`, `uG`, `uV`: the field, group and carrier in Gallagher's formula.

## Scope

- Only p-adic fields are covered. The archimedean, equal-characteristic and
  global cases of Tate §2.3 are outside this module, and so is (2.3.5).
- Tate (3.4.8) for the actual local constants, with additive characters
  `ψ ∘ Tr_{E'/E}`, is not stated here. The published system specification
  `Langlands.LocalFactor.NonabelianSystem` contains degree-zero induction as part
  of its system property. It uses the Library's common-closure model of
  extensions, not the embedding model of this module. The arbitrary-degree
  correction for such systems is a separate submission,
  `Langlands.LocalFactor.Inductive.SystemStatement`. This module neither imports
  it nor depends on it.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: J. Tate,
  *Number theoretic background*, Corvallis Part II (1979). PDF page = printed
  page + 9.
  - §1 opening, printed p.3 (PDF p.12): `G^{ab} = G/G^c` with `G^c` the closure
    of the commutator subgroup; the transfer `G^{ab} → H^{ab}` for a closed
    subgroup `H` of finite index; the reciprocity isomorphisms
    `r_E : C_E → W_E^{ab}` of topological groups.
  - (W3), printed p.4 (PDF p.13).
  - (2.3.1), printed p.11 (PDF p.20).
  - (2.3.2), printed pp.11–12 (PDF pp.20–21).
  - (2.3.3) and (2.3.4), printed p.12 (PDF p.21).
  - (3.3) and (3.3.2), printed p.14 (PDF p.23): `L` is inductive;
    `L(V) = det(1 - Φ | V^I)^{-1}` with `Φ` an inverse Frobenius.
  - (3.4.1), printed pp.14–15 (PDF pp.23–24): the characters `ψ ∘ Tr_{E/F}`.
  - (3.4.8), printed p.15 (PDF p.24): degree-zero inductivity of local constants.
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  P. Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973).
  - §1.1, printed p.507 (PDF p.7): virtual representations, dimension, determinant
    and induction for an arbitrary group over a field `K`.
  - Proposition 1.2 (Gallagher), printed p.508 (PDF p.8): the determinant of an
    induced representation, in degree zero and with `ε^{dim ρ}` in general.
  - Proposition 1.5, printed p.510 (PDF p.10): degree-zero Brauer theorem, used
    in Tate's proof of 2.3.1.
  - Proposition 3.8 (ii), printed p.530 (PDF p.30), with Lemma 3.9, printed
    p.531 (PDF p.31): inductivity of the local L-function and the cyclic
    determinant identity used in its proof.

## Dependencies and status

Imports: `Langlands.LocalFactor.Inductive.Definitions` (companion, Worker 33,
published in the Library),
`Langlands.HarmonicAnalysis.CharacterTransport` (Worker 20, trace characters),
`Langlands.LocalFactor.Euler.Definitions` (Worker 20, the Euler polynomial
`det(1 - X A)`), `Langlands.ClassFieldTheory.Local.Transfer` (Library, the
continuous transfer on topological abelianizations),
`Langlands.Weil.Representation.Determinant` and
`Langlands.Weil.Representation.Invariants` (Library), and Mathlib's
`Mathlib.GroupTheory.Transfer`.

A full development check in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed29652`) compiled both modules with no errors or
warnings. Inspection of `InductiveFunctionsStatement` reports a definition
returning `Prop`, with universe parameters `u v uK uG uV` and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. Compilation does not establish
the truth of these statements. Independent semantic review is required.
