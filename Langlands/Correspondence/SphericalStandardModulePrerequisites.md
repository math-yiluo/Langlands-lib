# Ordered spherical generation and tempered realization

Author: Worker 1761.

These are two proposition-valued proof obligations, not assumptions or proved
classification results. They separate the spherical-vector argument from the
construction of a tempered datum for the actual normalized upper-Borel
principal series. All declarations are in `Langlands.Correspondence`.

`OrderedUnramifiedSphericalGenerationStatement F` says that every invariant
subspace of the principal series of an ordered tuple `z` is the whole
representation if its own maximal-compact fixed space is nonzero. The norm
order is weak, so repeated parameters and equal norms are included. Every
positive rank is quantified; no irreducibility of the principal series,
unitarity, or genericity is required.

This is a reformulation of spherical cyclicity using the one-dimensional
fixed space of the principal series. Its original source is Nadir Matringe,
*Essential Whittaker functions for GL(n)*, Documenta Mathematica 18 (2013),
1191–1214, Corollaries 1.1–1.2 on printed page 1200. In the retained folder
`matringe-2013-essential-whittaker`, the file
`Matringe--Essential Whittaker functions for GL(n)--2013.pdf` has that page
at PDF page 10 (one-based). The convention is normalized induction from the
standard upper parabolic, described in §1.2; “Langlands' type” orders real
character exponents decreasingly. As the Library uniformizer has absolute
value `q⁻¹`, this means increasing norms of the uniformizer values. A
subrepresentation with a nonzero fixed vector then contains the entire
one-dimensional fixed space, and cyclicity forces it to be the whole
principal series. This explains the reformulation; the Lean file does not
prove cyclicity or this correspondence.

`OrderedUnramifiedTemperedRealizationStatement.{uF,uA} F` asks, for every
weakly ordered tuple, for a tempered Langlands datum whose actual standard
module is equivalent to that actual principal series. Its tempered blocks
have carrier universe `uA`, independent of the field universe `uF`; the
standard module has carrier universe `max uF uA`. The equivalence is allowed
between different carrier universes. No spherical quotient or prescribed
representation is input or output.

The second obligation is an internal decomposition of
`SphericalTemperedStandardModuleStatement`, using the existing
`TemperedLanglandsDatum` and `principalSeriesOfTuple` definitions. Grouping
equal-norm characters is the intended construction: the resulting blocks
must actually be irreducible and analytically tempered, and their real
determinant exponents must strictly decrease. None of those facts is proved
by introducing this proposition. Its wording does not assert that every
possible datum presenting the same irreducible quotient has this standard
module.

`SphericalStandardModulePrerequisitesStatement` is the conjunction of the
two obligations. It is an internal interface for the conditional reduction;
it neither replaces nor weakens the original target.
