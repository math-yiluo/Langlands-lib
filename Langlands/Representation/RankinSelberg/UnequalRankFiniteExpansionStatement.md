# Finite Schwartz expansion of unequal-rank block coefficients

Author: Worker 180. The statement and intended reduction were specified by
Worker 329.

The module defines the proposition
`Langlands.RankinSelberg.UnequalRankFiniteExpansionStatement.{uF,uV} F T n j k`.
It imports the published `RankinSelberg.AnalyticStatement` and uses its actual
Whittaker coefficient models and the matrices from `QuotientIntegrals`.
This is a statement target, with no implemented proof.

## Quantifiers and topology

For every prime natural number `p` with `[Fact p.Prime]`, the parameters are
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and arbitrary
natural numbers `n`, `j`, and `k`. The proposition installs exactly
`T.topology`, `T.valuativeRel`, and `T.localField`. In particular, the character,
compactness, and Schwartz–Bruhat functions use the supplied topology, without
replacing it by canonical data.

Write `t = n + 1` and `r = n + (j + k + 1) + 1`. The proposition quantifies
over every:

- `ψ : UnitaryAdditiveCharacter F.Carrier`, a continuous nontrivial additive
  character valued in the unit circle;
- `V : Type uV` with `AddCommGroup V` and `Module ℂ V`;
- representation `π : Representation ℂ (Langlands.GeneralLinear r F.Carrier) V`
  satisfying
  `IsOfWhittakerType (n + (j + k + 1))
  (standardCharacter ψ (n + (j + k + 1))) π`;
- `ℓ : glFunctionals ψ (n + (j + k + 1)) π` with `ℓ.val ≠ 0`;
- `f : (coefficientModel π ℓ).toSubmodule`.

The field and representation carrier universes `uF` and `uV` are independent.
The published Whittaker-type condition means admissibility, finite generation
over the group algebra, and a one-dimensional space of functionals for the
specified standard character. Admissibility includes smoothness.
Irreducibility and a unitary central character are not assumed. A coefficient
model element is an actual function `f.val.val : GL_r(F) → ℂ`, obtained from
the same representation and functional by `h ↦ ℓ(π(h)v)`.

## Conditional pointwise identity

The explicit premise is

```lean
∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier),
  IsCompact C ∧ ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) x,
    f.val.val (unequalRankMatrix j k g x) ≠ 0 → x ∈ C
```

Thus one compact set contains the nonzero rectangular support for all `g`.
It can depend on the preceding data, including `f`, but is chosen before
`g` and `x`. The statement does not supply this premise.

The conclusion is exactly

```lean
∃ (m : ℕ)
  (φ : Fin m → SchwartzBruhat (Matrix (Fin j) (Fin (n + 1)) F.Carrier))
  (fs : Fin m → (coefficientModel π ℓ).toSubmodule),
  ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier) x,
    f.val.val (unequalRankMatrix j k g x) =
      ∑ i : Fin m, φ i x * (fs i).val.val (appendIdentity n (j + k + 1) g)
```

Here `SchwartzBruhat` is the published type in
`Langlands.HarmonicAnalysis`: locally constant, compactly supported
complex-valued functions. The finite family is chosen before both variables.
Every `fs i` belongs to the original coefficient model for `π` and `ℓ`.
The equality is pointwise for every `g` and `x`, including outside `C`.

The matrix on the left has blocks

```text
[ g   0     0       ]
[ x   I_j   0       ]
[ 0   0     I_(k+1) ],
```

where `x` has `j` rows and `n + 1` columns. By the published definition it is
`appendIdentity n (j + k + 1) g * rectangularUnipotent j k x`.
The right side evaluates larger-group coefficients on
`diag(g, I_(j+k+1))`. Both sides stay in `GL_r(F)`.
All `j = 0`, `k = 0`, and positive rank gaps `r - t = j + k + 1`
are retained. In particular, `j = 0` gives the zero-dimensional rectangular
space, and `j = k = 0` is the corank-one case.

## Derived provenance and intended proof route

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, source ID `jpss-1983-rankin-selberg`. The retained scan is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385–386 and 393–394 were read visually
(zero-based PDF indices 19–20 and 27–28).

Section 2.1, printed pages 385–386, specifies admissible finite-type
representations of Whittaker type and defines their coefficients by equation
(3) on page 386. It also records stability under right translations.
Section 2.2 on page 386 uses smooth functions in the mirabolic restriction
space. These are the smooth representation and right-translation conventions
used here; the compact support modulo the unipotent group in Section 2.2 is
not substituted for this statement's uniform rectangular-support premise.

In the unequal-rank part of the proof of Theorem 2.7, printed page 393
states that a nonzero block coefficient forces `x` into a compact set
independent of `g`, referring to Section 2.6. It then reduces the integrals
to a finite sum. Equation (7) on printed page 394 gives the resulting
diagonal restriction integrals, still using coefficients of the original
larger representation.

The displayed pointwise Schwartz expansion in this module is a derived
interface making that finite reduction precise; it is not a displayed
theorem of JPSS. Its intended elementary argument is as follows. Smoothness
provides an open stabilizer for a vector representing `f`. Pulling this
back along the continuous rectangular-unipotent additive subgroup and
shrinking gives a compact open additive subgroup `U` of the rectangular
matrix space such that
`f(D(g)u(x + a)) = f(D(g)u(x))` for every `g`, `x`, and `a ∈ U`.
Here `D(g)` is the diagonal inclusion and `u(x)` the rectangular unipotent.
The identity `u(x + a) = u(x)u(a)` makes this invariance uniform in `g`.

Compactness of `C` leaves finitely many distinct cosets `x_i + U` meeting
`C`. Their characteristic functions are Schwartz–Bruhat functions.
Take `fs i` to be the right translate of `f` by `u(x_i)`; it remains
in `coefficientModel π ℓ`. On the coset `x_i + U` the required value is
`(fs i)(D(g))`. Outside their union the support premise makes the left
side zero and all characteristic functions vanish. Disjointness of
distinct cosets yields the finite identity. This paragraph explains the
provenance and proposed proof route; none of these steps is proved by
this proposition definition.

The separate compact-support statement task
`7cd83342-a96b-46d7-9933-35f7dc7ca187` is a future supplier of the premise;
no unpublished declaration from that task is imported or assumed here.
No measures, Haar normalization, second representation, spectral parameter,
convergence, or rationality occur in the assertion. For a later integral
consumer the expansion keeps the same larger group and hence the same
determinant exponent `s - (r - t)/2` in equation (7). It makes no change
to an integral with a different rank gap.

## Validation

The proposition passed a Lake build and declaration inspection in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors and warnings.
Inspection reports `statement_returns_prop = true`, independent universe
parameters `uF` and `uV`, and only `propext`, `Classical.choice`, and `Quot.sound`.
These checks certify elaboration and allowed assumptions, not a proof of the
proposition.
