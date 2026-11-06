# Scheme pushouts along a closed immersion and an integral morphism

`Langlands.AlgebraicGeometry.IntegralSchemePushoutStatement.{u}` states
selected conclusions of the Stacks Project, Proposition 37.67.3 (Tag
0E25), under all the hypotheses of Situation 37.67.1 (Tag 0ECI).
It is a proposition definition; this file supplies no proof.

For arbitrary schemes `X`, `Y` and `Z` in universe `u`, let `i : Z ⟶ X`
be a closed immersion and `j : Z ⟶ Y` an integral morphism. The third
hypothesis says explicitly that for each underlying point `y : Y` there
is an affine open `U` of `X` containing the image under `i` of every
point in the fibre of `j` over `y`. The quantification over `z : Z` is
exactly the set inclusion `j⁻¹({y}) ⊆ i⁻¹(U)` in Situation 37.67.1;
it does not require the fibre to be finite.

The conclusion supplies an actual scheme `P` in the same universe and
actual maps `a : X ⟶ P` and `b : Y ⟶ P`. The square with top arrow `i`,
left arrow `j`, right arrow `a` and bottom arrow `b` is both a categorical
pushout and a categorical pullback in `Scheme`. The map `a` is integral
and the map `b` is a closed immersion. The pushout universal property
tests maps to arbitrary schemes.

There is no additional finiteness, affine, noetherian, reduced,
separatedness, flatness or projectivity hypothesis on the schemes. In particular nonreduced schemes are retained.
The statement uses the existing Mathlib objects and predicates and does
not introduce a pinched scheme, a conductor, or a chosen model.

## Original source and provenance

The registered original is
`stacks-affine-integral-scheme-pushouts-2026-11-06`, an HTML snapshot of
the Stacks Project retained under
`literature/Stacks Project - Affine and integral scheme pushouts, Tags 0ET0 07RS 0ECI 0E25 0ECH (HTML snapshot 2026-11-06)`.
Its folder SHA-256 is
`9d19931877f5d355ef57ff7ab05e2283e39200a03a656fa7c4c3f59ed9153c7e`.
The precise passages are:

- `0ECI.html`, [Situation 37.67.1](https://stacks.math.columbia.edu/tag/0ECI),
  all three hypotheses;
- `0E25.html`, [Proposition 37.67.3](https://stacks.math.columbia.edu/tag/0E25),
  the existence, cartesian-square, integral-map and closed-immersion
  assertions.

This formulation has derived provenance because it selects these
conclusions from the source proposition and suppresses the unused
structure maps to a common base scheme. Every span of schemes has those
structure maps to `Spec ℤ`; the source asserts the pushout in the
category of schemes. No sheaf-of-rings identification from the source
proposition is asserted here.

Workers 139 and 1603 read the complete original situation and proposition
and the six comments on the section in `0ECH.html`. The source-specific errata
directories checked in the workspace, project and supplied Library were
absent. The comments correct the direction of `Z ⟶ Y` and occurrences
of `Y ∐_Z X`; the formulation uses those directions.

## Remaining application boundaries

The affine statement `AffineSchemePushoutStatement` concerns the
spectrum of a given ring pullback with one surjective map. This global
statement instead requires the displayed fibre-neighborhood hypothesis
and supplies a scheme pushout. A ring pullback identity alone supplies
neither its global input schemes nor this hypothesis.

The finite-set affine-neighborhood property used in the
Faltings–Chai conductor argument remains a separate obligation. This
statement does not claim its preservation, construct a normalization or
conductor square, identify a pushout with a previously given algebraic
space, or classify rigidified families. It therefore supplies no
abelian-scheme or Picard representability result.

The formulation and initial exposition were supplied by Worker 139.
Worker 1603 checked the source correspondence and prepared this pair.
