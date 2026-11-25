# Berkovich's ordinary equivariant spectral sequences for compact bases

## Source

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), [Theorem 1.6.1(ii), p. 13](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=13),
printed and PDF page 13. Registered literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

For a compact analytic `G`-space, the source first compares `H^q(X{G}, F)`
with `H^q(X, b^*F)`, then displays, on both the étale and quasi-étale sites,

\[
E_2^{p,q}=H^p(G,H^q(X,b^*F)) \quad\Longrightarrow\quad H^{p+q}(X(G),F).
\]

This module states the Library-model version of the **spectral-sequence
clause** of (ii) and the smoothness of the canonical action needed to form
its second page. The comparison clause is separately stated in
`AnalyticEtaleGlobalComparison.Statement` and
`AnalyticQuasiEtaleGlobalComparison.Statement`. Here their conclusions are
not assumed. There is no proper-support or compact-support functor in this
module: compactness is a condition on the base of the ordinary cohomology.

The equivariant functors are taken in the same Library models as in
[Statement.md](Statement.md). The manuscript uses sheaves on its
actual equivariant sites and Theorem 1.4.2, pp. 8–9, identifies those
sheaves with smooth `G`-sheaves there. The formal comparison needed to
transport the model functors to the manuscript sites remains open. The
quasi-étale version here uses ordinary cohomology for `quasiEtaleTopology`
and the equivariant model for `twistedQuasiEtaleTopology`; there is no
identification with the manuscript's topology or with the compact-probe
replacement.

## Statements

`AnalyticEtaleCompactBaseSpectralSequenceStatement` and
`AnalyticQuasiEtaleCompactBaseSpectralSequenceStatement` are propositions in
`Langlands.Cohomology.AnalyticGlobalSpectralSequence`. Their parameters are
those of the two §1.2 statements in [Statement.md](Statement.md): the action
on `X` is continuous and over the fixed complete ultrametric normed field
`K` (the manuscript allows base-field automorphisms, §1.1, pp. 1–2); the
module coefficients use one commutative ring `R` (for abelian sheaves take
integer coefficients, with a universe lift if needed); and the
smallness and respective refinement instances are retained. Here there is
the additional hypothesis `IsCompactSpace X`, meaning compact and Hausdorff
in the analytic-space terminology. The propositions quantify over a model
of `D(SmoothRep R G)` at morphism universe `w` and over a sheaf `F` on the
respective twisted site in the `EtaleGSheaf` or `QuasiEtaleGSheaf` model.

The spectral sequence is `spectralSequence D A` as in §1.2: `D` is the image
of the model's derived smooth sections `RΓ(X{G}, F)` in the full derived
category, and `A` is the trivial representation on `R`. The second-page coefficient object is different
here. For each `q : ℕ` the proposition gives smoothness `hs q` of
`etaleRestrictionCohomologyAction ρ R q F` or
`quasiEtaleRestrictionCohomologyAction ρ R q F`. These are the canonical
representations on the actual `H^q(X,b^*F)` defined by the twisted-site
action on ordinary cohomology, not representations chosen or transported
from a comparison isomorphism. The proposition uses the same action in
`SmoothRep.of _ (hs q)` and identifies the second page for `p,q : ℕ`
additively with `Abelian.Ext.{w} A (SmoothRep.of _ (hs q)) p`. This Ext in
smooth `R`-modules is derived smooth invariants, by the trivial-source Hom
identification in `AnalyticGlobalComposite.InvariantsHom`.

The other conjunct is `FirstQuadrantAbutmentStatement D A H`, with `H n`
the underlying additive group of derived invariant sections in degree `n`
in the same model. It identifies the abutment with this model value of
`H^n(X(G),F)` and includes the vanishing outside the first quadrant on page 2,
the finite truncation filtration and the stable-page identifications. The page and abutment
identifications are additive, not asserted to be `R`-linear or natural
families. No additional assumption on `G` such as compactness is made.

## Provenance of the derived presentation

These are statements, not proofs. The intended route follows the source:
use the §1.2 spectral sequence, then replace `H^q(X{G},F)` on page 2 by
ordinary cohomology via the compact-base comparison. In Lean, the
comparison maps intertwine the actual actions by `AnalyticRepComparison`.
`AnalyticRepSmoothness` packages each target as a smooth representation
under surjectivity and gives `etaleComparisonSmoothIso` and
`quasiEtaleComparisonSmoothIso` under bijectivity. The separate comparison
statements give exactly those bijections in this setting. The
quasi-étale one is proved in the Library as
`Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.analyticQuasiEtaleGlobalComparison`
(`AnalyticQuasiEtaleGlobalComparison/Proof.lean`); this module imports
neither comparison statement nor its proof. Ext in its
second variable then carries the resulting smooth isomorphisms to the
claimed identifications. The convergence assertions stay unchanged. This
explains the route without taking any page isomorphism, compact-base
comparison, or smoothness as a theorem hypothesis.
