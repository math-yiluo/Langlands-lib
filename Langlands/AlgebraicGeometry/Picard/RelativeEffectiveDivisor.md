# Relative effective Cartier divisors as actual closed subschemes

Author: Worker 1543.

For an actual ideal sheaf datum `I : X.IdealSheafData`,
`Langlands.AlgebraicGeometry.Picard.IsEffectiveCartierIdeal I` means that
the actual module sheaf
`StructureKernelModule.kernelModule I.subschemeι` is locally free of rank
one. This module is the sectionwise kernel of the structure map
`O_X → (I.subschemeι)_* O_D`; it is not an independently supplied line
bundle. Mathlib's `ker_subschemeι_app` identifies its ideal on each affine
open with the ideal of `I`. Thus this predicate says exactly that the ideal
of the actual closed subscheme is invertible.

`EffectiveCartierDivisor X` is the subtype of such ideals. Its `subscheme`
and `ι` are Mathlib's closed subscheme and closed immersion attached to that
same ideal. Equality is equality of ideals, so different presentations of
the same closed subscheme are not additional divisor data.
`idealLineBundle` packages the actual kernel as `O_X(-D)`;
`lineBundle` is its internal dual `O_X(D)`. The canonical `idealInclusion`
is a monomorphism by the published kernel universal property. Its
quasi-coherence follows from the published quasi-coherence theorem for
the structure-map kernel of an affine morphism, applied to the closed
immersion.

The `canonicalSection` of `O_X(D)` is this inclusion viewed as a global
section of the internal Hom sheaf. The displayed evaluation identity is
definitional: evaluating this dual section on a global ideal section gives
the ideal inclusion. This module does not yet prove the comparison with
the separate tensor-evaluation map `LineBundle.evalSection`.

For any morphism `f : X ⟶ S`,
`IsRelativeEffectiveCartierIdeal f I` is the conjunction of the effective
Cartier condition and `Flat (I.subschemeι ≫ f)`.
`RelativeEffectiveDivisor f` is the subtype of actual ideals satisfying
this predicate. Its structural morphism `toBase` is flat by that
predicate. These definitions impose no noetherian, proper, projective,
smooth or finite-presentation assumption, and impose no additional
condition on `f`. Every scheme is in universe `u`.

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), p.22, paragraph 3.1 and Definition 3.3. Paragraph 3.1 defines
effective Cartier divisors by invertible ideals, identifies the ideal with
`O_X(-D)`, and describes the canonical section of `O_X(D)` from its ideal
inclusion. Definition 3.3 requires the closed subscheme to be flat over
the base. The registered original is
`kleiman-2005-picard-scheme-arxiv-math0504020v1`; pp.22–23 were read, and no
corresponding project erratum was found. Kleiman's surrounding conventions
restrict to locally noetherian schemes; the definitions here use the same
invertible-ideal and flatness conditions on arbitrary schemes.
The ideal-kernel representation and internal Hom implementation are
internal realizations using the published Library constructions.

Base-change stability, the divisor presheaf, openness in the Hilbert
scheme, the Abel map and Picard representability are separate obligations.
In particular, arbitrary base-change stability is not included as a field
or hypothesis in the definition.
