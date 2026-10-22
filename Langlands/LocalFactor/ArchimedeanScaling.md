# Explicit character and measure changes for archimedean epsilon blocks

This module extends the published `RealCharacterData` and
`ComplexCharacterData` constructors with callable epsilon factors for an
explicit additive-character scalar and a positive multiple of the fixed
standard Haar measure. It covers the real character, complex character,
and actual two-dimensional real induction blocks of
`Langlands.LocalFactor.ArchimedeanAttachment`.

The scalar `a` is a unit of the relevant field. The finite scale `c` has
type `NNReal`, with a certificate `hc : 0 < c`. Each epsilon constructor
returns a complex unit for every spectral parameter `s : Complex`.
The spectral convention is
`epsilon(s,V,psi,mu) = epsilon(V tensor |.|^s,psi,mu)`, where the absolute
value is normalized for the local field. No restriction on `s` or the
character exponent is imposed.

## Actual harmonic inputs

`realStandardCharacter` bundles Mathlib's continuous nontrivial
`Real.fourierChar`, namely `x -> exp(2*pi*i*x)`.
`complexStandardCharacter` uses the published `tracePullback` construction
with the actual field trace `Algebra.trace Real Complex`. Thus it is
`z -> exp(2*pi*i*Tr(z))`, with `Tr(z)=2*Re(z)`. The module supplies the
finite-dimensional module-topology instance locally; it adds no topology
or continuity assumption.

`realStandardMeasure` is Lebesgue measure. `complexStandardMeasure` is
twice Mathlib's Euclidean volume on the complex plane, namely `2 dx dy`.
Their regular additive Haar certificates come from Mathlib and the
published positive-scaling operation.

`realScaledCharacter a` and `complexScaledCharacter a` apply the published
character scaling operation. Their evaluation lemmas give respectively
`Real.fourierChar(a*x)` and `Real.fourierChar(Tr(a*z))`.
`realScaledMeasure c hc` and `complexScaledMeasure c hc` multiply the
fixed standard measure by `c`. The measure projection lemmas give
`c • volume` and `(c*2) • volume`, respectively. In particular, changing
`a` does not silently replace the measure by a self-dual one.

## The three callable epsilon constructors

Write `e` for the real datum's parity, `m` for the complex datum's weight,
and `chi` for its existing continuous multiplicative character. Write
`|a|` for the ordinary real absolute value and `norm(a)` for the Euclidean
complex norm.

| Constructor | Complex value |
| --- | --- |
| `RealCharacterData.epsilon d a c hc s` | `c * chi(a) * |a|^(s-1) * i^e` |
| `ComplexCharacterData.epsilon d a c hc s` | `c * chi(a) * norm(a)^(2*(s-1)) * i^abs(m)` |
| `ComplexCharacterData.realInducedEpsilon d a c hc s` | `c^2 * (sign(a)*chi(a)) * |a|^(2*(s-1)) * i^(abs(m)+1)` |

In the last row `a` is a real unit and `chi(a)` means its value after the
explicit inclusion `realToComplex`. The real induction rank is two even
when `m=0`. The extra standard induction phase `i` remains present.
The complex block's exponent has a factor two because its normalized
absolute value is the square of the Euclidean norm; its representation
rank and its Haar-scale exponent are still one.

`realSign a` constructs the unit with complex value `a/|a|`.
`ComplexCharacterData.realInducedDeterminant d a` is the explicit unit
`realSign a * chi(realToComplex a)`. The module proves its value formula.
This is the determinant expression from the published presentation
statement. Its mathematical derivation uses the actual induction action:
on `ofComplex z` the diagonal determinant is `chi(z)*chi(conj(z))`, and
on `j` the matrix `[[0,1],[chi(-1),0]]` has determinant `-chi(-1)`.
The explicit real abelian coordinate is `z*j^b -> (-1)^b*norm(z)^2`,
so the resulting scalar expression is `sign(a)*chi(a)`. This derivation
needs no identification with a separately chosen reciprocity map.
The present Lean module constructs the scalar expression; it does not
add a theorem equating it to the determinant on every Weil-group element.

The existing polar equations determine the character values in the table:
`chi(x)=sign(x)^e*|x|^t` in the real case and
`chi(z)=(z/norm(z))^m*norm(z)^(2*t)` in the complex case. These are
certificates in the already published data types, not hypotheses about
epsilon. The expressions are precisely the singleton-block specializations
of Worker 33's published presentation formulas, with trivial powers and
singleton products simplified.

## Implemented laws and proof route

The `coe_epsilon` and `coe_realInducedEpsilon` lemmas expose the three
formulas above by definitional equality. The private helpers
`positiveScale` and `positivePower` construct complex units from positive
real numbers and their complex powers. Positivity and the nonzero unit
`a` prove that every complex-power base is nonzero. Mathlib's
`Complex.cpow_ne_zero_iff` then supplies nonvanishing at every exponent.
The explicit `epsilon_ne_zero` lemmas are projections of the resulting
unit certificates.

The `differentiable_epsilon` and `differentiable_realInducedEpsilon` lemmas
prove entire dependence of the complex values on `s`. Their proofs use
holomorphy of a complex power with a fixed nonzero base, composed with
`s-1` or `2*(s-1)`, followed by constant multiplication. No branch-cut
hypothesis in the variable `s` is needed.

The `epsilon_standard` and `realInducedEpsilon_standard` lemmas identify
the unit at `a=1,c=1` with the published standard epsilon, for every `s`.
They use character evaluation at one and `1^s=1`.
The measure-scaling lemmas prove that replacing `c` by `b*c`, for
positive `b`, multiplies the complex value by `b` in each rank-one case
and by `b^2` in the induced case. Their proofs expand the value formulas
and use polynomial identities. These ranks agree with the published
representation-rank theorems.

The L-factors remain the published reciprocal-entire constructions;
they have no additive-character or Haar-scale arguments. This module
adds no alternative L-factor or numerical value at a pole.

## Original source and provenance

The source is John Tate, *Number theoretic background*, Corvallis Part II
(1979), registered as `tate-1979-number-theoretic-background`.

- Retained original:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
- SHA-256:
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- Equations (3.2.2) and (3.2.3), printed p.13/PDF22: positive Haar
  scaling by `c`, and fixed-measure character scaling by
  `chi(a)*||a||^(-1)`.
- Equations (3.2.4) and (3.2.5), on the same page: the standard plus
  characters, real Lebesgue and twice-complex-area measures, and the
  phases `i^e` and `i^abs(m)`.
- Equations (3.4.3)--(3.4.5), printed p.15/PDF24: measure scaling by
  `c^rank`, character scaling by `det(V)(a)*||a||^(-rank)`, and
  standard archimedean spectral twisting with conductor and standard
  character scale equal to one.
- Section (2.3.4), printed p.12/PDF21: the determinant rule under
  degree-zero induction. The concrete determinant expression here is
  also obtained directly from the already published action matrices as
  explained above.

These pages were read directly for this extension. For a spectral twist,
`det(V tensor |.|^s)(a)=det(V)(a)*||a||^(rank*s)`.
Combining this with (3.4.4) gives the exponent `rank*(s-1)`.
For a complex field replace `||a||` by `norm(a)^2`. Positive measure
scaling is independent and contributes `c^rank`. The standard phases
and the real induction correction are reused from the published
`ArchimedeanAttachment` constructions. Thus the three formulas are
derived from Tate's conventions rather than quoted verbatim in his
parameter notation.

The Lean constructors are explicit arithmetic definitions and their
construction laws. They do not assume or prove the existence of a
nonabelian epsilon system, nor a comparison with such a system.
They do not select `a` from an arbitrary additive character, select `c`
from an arbitrary Haar measure, classify representations, or descend
factors to isomorphism classes. Finite-presentation independence remains
a separate theorem; its statement is not imported or assumed here.

## Dependencies and authorship

The direct project imports are the published
`Langlands.LocalFactor.ArchimedeanAttachment` and
`Langlands.HarmonicAnalysis.CharacterTransport`, available at Library
`d7cf4d2d2f040f4dfa5ab22d869d51196351d821`. The character, representation,
standard factor, and harmonic-transport constructors are reused by name.
Mathlib supplies Lebesgue measure on the complex plane, holomorphy of
complex powers, and finite-dimensional module topology.

Worker 33 authored the determinant/rank/polar expressions reused from
`ArchimedeanPresentationStatement` and is a coauthor. Worker 40 adds the
callable unit-valued block functions, actual standard/scaled harmonic
inputs, and the construction laws. Worker 20's harmonic transport
constructors are reused from the published Library.

Environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
