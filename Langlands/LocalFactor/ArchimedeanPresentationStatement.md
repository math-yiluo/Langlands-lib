# Independence of archimedean arithmetic factor presentations

Worker 33 authors the proposition
`Langlands.LocalFactor.ArchimedeanFactorPresentationIndependenceStatement`.
It asserts that isomorphic finite presentations by the actual archimedean
Weil representations give the same separate L- and epsilon-factors.
All factor expressions are explicit. Their equality is a conclusion;
neither a classification theorem nor the existence of a factor system is
assumed.

This is a statement contribution, with theorem proofs separate. It covers
choice independence on actual finite presentations. It does not claim that
every representation admits such a presentation. In particular, it does
not confuse arbitrary continuous representations with semisimple ones.
Completeness of semisimple presentations, reciprocity identification, and
construction of a descended callable factor on all intended parameter
classes remain separate obligations.

## Actual representations and input equations

The representation constructors are Worker 2's
`Langlands.Weil.Archimedean.complexCharacter`, `realCharacter`, and
`realInducedCharacter`. The first two act on the complex line; the last acts
on `Complex × Complex` and is identified by a proved intertwining equivalence
with the actual equivariant-function induction model. Its restriction to
the complex subgroup is the sum of a character and its conjugate pullback;
the standard element `j` acts by `[[0,1],[chi(-1),0]]`.
No additional representation-existence or continuity assumption is supplied.

A complex datum consists of a continuous homomorphism
`chi : ComplexUnits -> ComplexUnits`, an integer `m`, and a complex number
`t`, with the explicit equation

```
chi(z) = (z / |z|)^m |z|^(2t).
```

Here `|z|` is the Euclidean norm. The normalized local absolute value is
its square. A real datum consists of a continuous homomorphism on real
units, a parity `e : Fin 2`, and a complex number `t`, with the equation

```
chi(x) = sign(x)^e |x|^t.
```

These equations specify input parameters for existing characters. They
assume no factor formula and no existence theorem. Nonunitary characters
are allowed, and no restriction on `Re(t)` occurs. The earlier published
archimedean abelian statement separately states classification of all
quasicharacters; it is not resubmitted or assumed here.

The complex presentation is a finite list of complex data. The real
presentation is a finite list whose entries are either real character data
or complex character data interpreted by actual real induction. The code
forms their actual representations using the published binary
`FiniteRepresentation.sum`, folded from the zero-dimensional representation
on `Fin 0 -> Complex`. Thus empty presentations are included.

All presented model carriers lie in `Type`. The comparison uses the actual
invertible complex-linear intertwiner
`FiniteRepresentation.Equiv`, not equality of parameter labels, equality
of characters, a basis, or an assumed equality of factors. The published
equivalence interface also supports comparison of these models with
representations in other carrier universes when the separate presentation
existence theorem is supplied.

## L-factors and standard epsilon constants

The normalized blocks are as follows.

| Actual block | L-factor | Standard epsilon constant |
| --- | --- | --- |
| Complex character `(m,t)` | `Gamma_C(s+t+|m|/2)` | `i^|m|` |
| Real character `(e,t)` | `Gamma_R(s+t+e)` | `i^e` |
| Real induction of complex character `(m,t)` | `Gamma_C(s+t+|m|/2)` | `i^(|m|+1)` |

The real additive character is `exp(2 pi i x)` with Lebesgue measure.
The complex additive character is `exp(2 pi i Tr(z))` with measure twice
Euclidean area. These are the plus Fourier conventions and their standard
self-dual measures. No further self-dual normalization is silently made
when the measure is scaled below.

The L expression is the product of Worker 20's published
`gammaReal.shift` and `gammaComplex.shift` constructors, combined by
`ReciprocalEntire.product`. Consequently it is an actual nonzero entire
reciprocal denominator and a punctured meromorphic germ at every point.
The theorem states equality in `ReciprocalEntire`; hence the entire
denominators and all resulting punctured germs agree, including at poles.
Numerical evaluation is available only on `RegularPoint`. The code never
asserts a finite Gamma value at a pole.

The epsilon expression is a separate finite product of the displayed
constants. It is not recovered only from gamma, and the L and epsilon
conclusions are stated separately.

The extra `i` for real induction is the correction for
complex-to-real induction. To compute it, use the actual decomposition
of induction of the trivial complex character into the trivial and sign
real characters: their standard epsilon constants have product `i`,
whereas the trivial complex character has constant `1`. Applying
degree-zero inductivity to `chi - 1` then gives the factor `i` for
induction of any character. The target retains this correction; it does
not infer arbitrary-degree equality from degree-zero inductivity alone.

Complex weight zero is deliberately allowed in real induced blocks.
That model is reducible. Its two real character factors obey

```
Gamma_C(s+t) = Gamma_R(s+t) Gamma_R(s+t+1),
1 * i = i.
```

Thus a presentation using the weight-zero induced block can agree with
one using its two one-dimensional constituents. The statement does not
declare every induced block irreducible. This case is essential for
independence across different finite presentations.

## Fixed Haar scaling and additive characters

For each complex presentation of rank `n`, the code also defines the
explicit expression

```
epsilon(ds, a, c, s)
  = c^n (product chi_j(a)) |a|^(2n(s-1)) epsilon_standard(ds).
```

Here `a` is a nonzero complex number and `c : NNReal` is positive. This
corresponds to the character `z -> exp(2 pi i Tr(a z))` and the fixed
measure `c` times the standard complex measure.

For a real presentation the rank is the sum of block ranks, one for a
real character and two for an induced block. Its explicit expression is

```
epsilon(ds, a, c, s)
  = c^n (product det_block(a)) |a|^(n(s-1))
      epsilon_standard(ds).
```

The real character block contributes `chi(a)` to this determinant
expression. The real induced block contributes
`sign(a) * chi(a)` with the real unit embedded into the complex units.
This is the determinant of the actual two-dimensional model expressed in
the explicit real abelian coordinate: the minus sign in the determinant
of the `j` matrix supplies the sign factor. This computation needs no
unproved identification of that coordinate with a reciprocity map.
The real character is `x -> exp(2 pi i a x)` and the fixed measure is
`c` times Lebesgue measure.

Each component states that these expressions are entire and nonzero for
every spectral parameter and every positive Haar scale. No integral
convergence domain is needed for these explicit epsilon expressions.
The same component then states that actual isomorphic presentations
give equal L-factors, equal standard epsilon constants, and equal scaled
epsilon expressions for every allowed `a`, `c`, and `s`.
Isomorphism is the sole representation-comparison hypothesis; equality
of ranks, determinant expressions or arithmetic factors is not assumed.

## Original sources and derivation

The original source is J. Tate, *Number theoretic background* (1979),
in Corvallis Part II:

- Section 2.2.2, printed p.10/PDF19: actual archimedean character and
  induction types, including the reducible weight-zero formula
  (2.2.2.1).
- Sections 3.1.1--3.1.2 and 3.2.2--3.2.5, printed pp.12--13/PDF21--22:
  the separate real/complex Gamma normalizations, the rank-one Haar and
  additive-character scaling rules, and the plus-convention epsilon
  phases with their standard measures. The complex Gamma includes its
  factor `2`. Its definition is printed with the label `(3.2.1)` at the
  top of p.13, in the sequence of local abelian L-factor definitions.
- Section 3.3.1, printed p.14/PDF23: extension of L to archimedean
  representations by irreducible decomposition, including real
  induction. The paragraph following 3.3.2 on the same page gives the
  duplication identity `Gamma_C(s) = Gamma_R(s) Gamma_R(s+1)`, used for
  the reducible weight-zero case.
- Sections 3.4.1--3.4.5 and 3.4.8, printed pp.14--15/PDF23--24:
  rank-one normalization and inductivity in degree zero (3.4.1),
  additivity (3.4.2), positive Haar scaling (3.4.3), additive-character
  scaling by the determinant (3.4.4), spectral twisting with
  `f(V) = delta(psi) = 1` for the standard archimedean characters
  (3.4.5), and induction in degree zero (3.4.8).

Registered literature ID: `tate-1979-number-theoretic-background`;
SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Retained original:
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
The earlier abelian normalization work visually checked the formula pages,
and PDF19 and PDF23--24 were read directly again for this presentation
target. For this submission the text of PDF19 and PDF21--24 was reread
against every locator above.

The polar-parameter notation is a translation of Tate's `z^(-N) omega_s`
and `x^(-N) omega_s`, with the spectral shifts made explicit. Complex
conjugation permits both signs of `m`, and the Gamma shift and phase use
its absolute value. The independence theorem is a derived formulation
of the uniqueness of the arithmetic factors on the stated actual finite
presentations. The list-fold implementation, the determinant expression
and the regular-domain representation are explicit implementation details;
they are not quoted verbatim from Tate.

## Dependencies and status

All three direct project imports were published under their original paths at
commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`, together with their own
published dependencies. Integration uses the canonical
`Langlands.LocalFactor.Archimedean.Definitions` path, retaining all declaration
names and mathematical bodies. The table records historical fingerprints
before migration; no draft or unpublished module is imported.

| Current import (original path where moved) | Historical Lean SHA-256 |
| --- | --- |
| `Langlands.Weil.ArchimedeanRepresentation` (Worker 2) | `32ba55eaf9ac19b6c4b9c6a48f390cce35991961d78aab0f5e83cd71e3ee20a2` |
| `Langlands.Weil.Representation.SumsTensor` (Worker 17) | `d5ce49ecda33a85b025d201c0cb114a98bbed8c65d36050aa6fc1b55cf42275b` |
| `Langlands.LocalFactor.Archimedean.Definitions` (formerly `Langlands.LocalFactor.Archimedean`, Worker 20) | `9f2a4b986dcdd37b16f6d7547896ee50b1fbe2f05f02451b872538aa8199d7f1` |

The representation Lean file is byte-identical to the version against
which this statement was first developed and checked; only its Markdown
was revised before publication. The published Markdown was read for this
submission, and the description of the three constructors above agrees
with it.

The local presentation expressions are available for coordination with the
arithmetic definition owner; they do not create a competing representation
carrier or claim an already descended arithmetic function.

The unchanged statement passed check
`8548543f-745f-4530-8344-c9da5a3a3f74` in the pinned environment
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) over
the published sources named above. The incremental Lake build and the
inspection of the closing declaration both terminated with exit code zero,
no errors or warnings, and quiet process trees. The closing declaration is
a definition returning `Prop`, has no universe parameters, and uses only
`propext`, `Classical.choice`, and `Quot.sound`. This reflects the fixed
small carriers of the concrete presentations described above. The
statement source SHA-256 is
`5c80fb482035cddb66f2972fdc110a1fbcbf8a660252ca74ceba170cae080d5e`;
the whole proposition fingerprint is
`009a9bf84c69e3bd82d95acb2a2532b137ddb5215c3d2b90e50e46946c775baa`,
identical to that of the first development check.

Independent semantic review accepted this statement contribution.
Compilation and target inspection do not prove the proposition. The theorem
proof is a separate obligation, and no callable descended factor or completion
of the broad arithmetic statement task is claimed.
