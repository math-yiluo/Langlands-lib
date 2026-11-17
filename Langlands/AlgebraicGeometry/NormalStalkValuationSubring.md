# Normal one-dimensional stalks as valuation subrings

This internal development supplies the local-ring embeddings used in
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4.
Its assertions are derived from Mathlib's function-field, separatedness
and local-ring structure theorems.

For an integral scheme `X`, `stalkImageSubring X x` is the actual range
of the canonical injection from the stalk at `x` into `X.functionField`.
`stalkEquivImage` gives a ring equivalence from the stalk onto this
subring, with explicit compatibility with the function-field inclusion.

When `X` is separated, `stalkImageSubring_injective` proves that distinct
points have distinct image subrings. An equality of the image subrings
gives a ring equivalence between the stalks that fixes their embeddings
into the function field. The two maps from the spectrum of either
stalk into `X` then agree at the generic point. Their common source is
reduced, so dominance of the generic map and separatedness imply that
they agree everywhere. Evaluation at the closed point identifies the
original points.

`stalkImageSubring_eq_top_iff_isField` characterizes the field case by
surjectivity of the fraction-field inclusion. The generic stalk has
image the whole function field; injectivity of the image-subring map
therefore gives `isField_stalk_iff_eq_genericPoint` for separated `X`.

`valuationRing_of_normal_dim_le_one` proves that a noetherian normal
local domain with `ringKrullDim ≤ 1` is a valuation ring. The field case
is included. The proof uses the fact that every nonzero prime ideal
must be maximal and hence equal the unique maximal ideal, then applies
Mathlib's local-domain characterization of valuation rings.
`discreteValuationRing_of_normal_dim_le_one` identifies the nonfield
case as a DVR.

For a stalk that is a valuation ring, `stalkValuationSubring` packages
its actual image as a valuation subring of the function field.
For a locally noetherian integral `X`,
`normalStalkValuationSubring` constructs this valuation subring directly
from normality of the stalk and its dimension bound.
`normalStalkEquivValuationSubring` retains the ring equivalence from the
stalk. On a separated `X`, the theorem
`normalStalkValuationSubring_isDiscreteValuationRing` proves that this
valuation subring is a DVR whenever the point is not generic.
All declarations apply in every universe. Construction of a semilocal
intersection and its scheme maps is a separate remaining step.
