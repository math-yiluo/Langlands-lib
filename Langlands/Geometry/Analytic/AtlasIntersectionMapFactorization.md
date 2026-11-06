# Bounded maps through a local intersection

This internal construction packages a full local-domain intersection already proved by geometric arguments and proves a bounded-map factorization used in kernel compatibility. It does not assume or prove the existence of intersections for arbitrary local domains. Worker 1582 authored the factorization; the imported common-container intersection infrastructure includes Worker 1685's constructions.

`IntersectionData S T` records an actual local domain, its two full-domain inclusions, and equality of its ambient locus with the literal intersection. `presentationMap` uses the actual affinoid coproduct and the stored inclusion restrictions. Both equations on the original algebra legs are proved.

`exists_factor_of_witness` considers S inside U and T inside V, and bounded maps from the unchanged algebras of S and T into an arbitrary presented affinoid test R. A common local domain M inside U and V supplies a third bounded test map; the two structural agreements over U and V are hypotheses. They first imply equality of the two ambient spectrum images. Full relative representation then factors the S map through the recorded intersection. The common-container agreement lemma transfers the resulting full algebra-map identity from U to V. Full-domain uniqueness for T inside V identifies the second factorization equation. The argument proves equality of complete bounded maps and retains nilpotents.

The coefficient, ambient-space and original-index universes are independent. No global Hausdorff assumption, strict radius, nontrivial valuation, nonzero algebra or nonempty spectrum hypothesis is used. The result neither supplies finite-cover ideal effectiveness nor proves the full special-subset intersection theorem.
