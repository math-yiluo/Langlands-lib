# Reflection of split tori along base maps admitting sections

Author: Worker 1354.

This is internal categorical infrastructure for specializing actual torus
splitting witnesses. It uses the published base-change coherence isomorphisms
and the existing `IsSplitTorus` definition, rather than a structural torus
splitting theorem.

The general section and algebraic-extension comparisons are reused from
`Torus.SplitDescent`. For a map `b : S' → S` with section `c : S → S'`,
`baseChangeSectionIso b c hc G` identifies the successive pullbacks with `G`;
its inverse gives the comparison in the other direction. The existing
`IsSplitTorus.of_baseChange_of_section` reflects splitness along this section.

The existing `IsSplitTorus.of_baseChange_of_isAlgebraic` reflects splitness
from an algebraic extension of an algebraically closed field, in arbitrary
universe `u`. It uses bijectivity of the algebra map and the corresponding
spectrum isomorphism. Finiteness, separability and normality of the extension
are not required.

`IsTorus.isSplitTorus_of_finiteGaloisSplitting` is an explicit conditional
adapter. It assumes the published proposition
`TorusFiniteGaloisSplittingStatement`, extracts its finite-dimensional splitting
extension, obtains algebraicity by Mathlib's finite-algebra instance, and applies
the preceding specialization. The Galois hypothesis is not needed by this step.

The algebraicity assumption is essential to this implementation. This module
does not show that an arbitrary `IsTorus` witness can be replaced by an
algebraic extension. It assumes, rather than proves, finite Galois splitting
in the final adapter; thus it does not establish the unconditional assertion
that every torus over an algebraically closed field is split. Finite splitting
and maximal-torus conjugacy remain separate structural obligations. All
results here are direct consequences of existing Library constructions and
Mathlib's algebraic-extension results; no new external mathematical
source is used.
