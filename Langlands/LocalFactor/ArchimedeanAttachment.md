# Arithmetic factors of presented archimedean Weil blocks

Worker 40 implements callable factor constructions from Worker 33's explicit
character-presentation expressions. This module uses actual continuous
characters and the published `complexCharacter`, `realCharacter` and
`realInducedCharacter` representations. Its factors use the published
`ReciprocalEntire` Gamma construction.

`RealCharacterData` specifies a continuous character `chi` on real units,
`e : Fin 2`, `t : Complex`, and the equation
`chi(x) = sign(x)^e |x|^t`. `ComplexCharacterData` specifies a continuous
character on complex units, `m : Int`, `t : Complex`, and the equation
`chi(z) = (z/|z|)^m |z|^(2t)`. The norm in the latter expression is the
Euclidean norm; its square is the normalized local absolute value.
These equations describe existing characters; they do not postulate factor
identities, classification, or existence of a local-constant system.
The trivial character provides an explicit input of either type.

The data has callable representation, L-factor, and standard epsilon
constructors. Real data uses the existing real character on the complex line.
Complex data has both the existing complex character on the complex line
and the existing two-dimensional real induction on `Complex × Complex`.
Their proved ranks and action equations are reused from the published
representation module. No representation is replaced by a formal label.

| Actual representation | Spectral L-factor | Standard epsilon |
| --- | --- | --- |
| Real character `(e,t)` | `Gamma_R(s+t+e)` | `i^e` |
| Complex character `(m,t)` | `Gamma_C(s+t+|m|/2)` | `i^|m|` |
| Real induction of complex character `(m,t)` | `Gamma_C(s+t+|m|/2)` | `i^(|m|+1)` |

The real additive character is `exp(2 pi i x)` with Lebesgue measure.
The complex additive character is `exp(2 pi i Tr(z))` with twice Euclidean
area. Epsilon values are constructed as complex units, with nonvanishing
proved from `i != 0`. The induced value retains the complex-to-real factor
`i`, and its product relation with the complex value is proved by the
successor law for powers. Weight zero is allowed; no irreducibility claim
is made. The trivial induced input has epsilon `i`.

Every L-factor is a nonzero entire reciprocal denominator, with punctured
meromorphic germs at all centers. The module proves the explicit pole
sets by translating the published Gamma pole criteria, and its evaluation
lemmas use `RegularPoint`. No value at a pole is exposed as a finite
complex arithmetic factor. The complex Gamma normalization retains its
factor `2`.

## Source correspondence and scope

The original source is John Tate, *Number theoretic background* (1979),
Corvallis Part II, literature ID `tate-1979-number-theoretic-background`.
Retained source:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
SHA256: `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The fingerprint was verified and PDF15,18--19,21--24,26 were read directly.
No source-specific erratum file is present in the current notes roots.

- Section 1.4.3, printed p.6/PDF15, and section 2, pp.9--10/PDF18--19,
  supply the actual archimedean groups and continuous representation setting.
- Section 2.2.2, p.10/PDF19, gives the character and induction types,
  including the reducible zero-weight induction.
- Sections 3.1.1--3.1.2 and 3.2.4--3.2.5, pp.12--13/PDF21--22,
  give the real/complex Gamma and standard epsilon formulas. The complex
  L definition has the printed label `(3.2.1)` at the top of p.13.
- Section 3.3.1, p.14/PDF23, specifies the L-factor for real induction.
  The following paragraph records Gamma duplication, which also explains
  the reducible zero-weight case.
- Sections 3.4.1--3.4.2 and 3.4.8, pp.14--15/PDF23--24, give degree-zero
  inductivity and additivity. Applying these to `chi - 1`, and using
  `Ind(1) = 1 + sign`, gives the induction correction `i`:
  the real trivial/sign phases have product `i`, and the complex trivial
  phase is `1`.

The polar convention is a derived translation of Tate's `x^(-N) omega_a`
and `z^(-N) omega_a`. For real parameters, `a=t+e`. For complex parameters
choose the embedding according to the sign of `m`, put `N=|m|`, and use
`a=t+|m|/2`. Thus no parity or weight shift is lost by the published
Tate-notation wrappers. The induction phase is a source-derived definition,
not a proof here of the existence or uniqueness of the nonabelian system.

These are factors of explicitly presented concrete blocks. No character
classification is assumed, no presentation is selected for an arbitrary
representation, and no function on isomorphism classes is constructed.
Independence of parameters/presentations, agreement with a local-constant
system, arbitrary additive characters and Haar scales, and factor
comparison theorems remain separate obligations. In particular the
construction does not turn Worker 33's independence proposition into
an assumption.

## Dependencies and authorship

Only `Langlands.LocalFactor.Archimedean.Definitions` and
`Langlands.Weil.ArchimedeanRepresentation` are imported, with their
published dependencies. Before the structural migration, their Lean/Markdown
pairs at the old paths and those of `ReciprocalEntire` and `Weil.Archimedean`
were verified byte-identical to Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. Integration changes the
archimedean import to its canonical path; the imported mathematical
declarations are unchanged.

Worker 33 authored the character data equations and block expressions in
the published `ArchimedeanPresentationStatement` pair. Worker 40
reuses those expressions with explicit compatibility fields and adds
callable constructions, unit-valued epsilon, representation-action
connections, pole/evaluation lemmas, and the elementary construction proofs.
Worker 33 is a coauthor of this contribution. The statement module
is not imported or used as a theorem.

Environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
