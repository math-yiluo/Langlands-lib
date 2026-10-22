# Multiplicative spectrum foundation target

Author: Worker 36.

`Langlands.Analytic.SpectrumPropertiesStatement` is a proposition definition
for the actual `BanachSpectrum` construction. It quantifies over arbitrary
normed commutative rings, with independent universes for scalars and
inequality index types. It does not assume any of its conclusions.

The source is Berkovich, *Non-archimedean analytic spaces* (Trieste lectures,
2009), Definition 1.2.3, Exercise 1.2.4 and the following prime-kernel
paragraph, Definition 1.2.5 and Fact 1.2.6, printed/PDF p.4;
Exercise 2.2.2(i), p.9, and (iv), p.10, for Laurent inequalities and the
neighborhood context.
Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
[author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf).

The target states:

- Evaluation into the real function space is a closed embedding, and the
  spectrum is compact and Hausdorff.
- Every point's actual seminorm kernel is prime.
- Pulling a point back along a scalar embedding gives exactly the norm on
  the scalar field, even if the target algebra has no `NormOneClass`.
- Every Laurent inequality locus is closed and compact. This part allows
  arbitrary index types and real thresholds.
- Every neighborhood of a point contains a compact Laurent locus defined
  by two finite lists and strictly positive thresholds, with the point
  in its interior.
- On a normed field itself, every spectrum point evaluates as the field
  norm.
- Pullback under any actual bounded ring map sends Laurent inequalities
  to the same inequalities applied to the images of their elements.

The target deliberately separates this topological scope from the
stronger source assertions requiring further constructions. It does not
include nonemptiness of the spectrum of a nontrivial Banach ring, nor an
analytic-domain universal property. Completeness is unnecessary for the
listed topology and kernel statements; the proof uses the actual closed
set of bounded seminorms. Scalar normalization and the pullback formula
are derived consequences, and the finite-neighborhood conclusion is the
topological inequality-set component of the source's affinoid statement.

This file imports only the spectrum definitions and Mathlib. In particular,
it does not import its proof or the auxiliary modules proving the target.
It must be independently accepted and currently published before a proof
task can name it as its Library target.
