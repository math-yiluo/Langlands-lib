# Exact equal-rank induced Jacquet lengths

This derived helper implements the additive Jacquet-length computation in the
proof of Renard, *Représentations des groupes réductifs p-adiques* (9 July 2026),
VI.5.4, printed pp.173–174 / PDF pp.179–180, using the actual filtration of
VI.5.3(iii), printed p.173 / PDF p.179.

`pointInducedJacquetObjectFiltration` constructs the actual ordered induced
Jacquet filtration, retaining its bijective enumeration, normalizer lifts,
source and target decompositions, and grade isomorphisms. It derives the
positive-simple-root comparison and Haar epsilon cancellation from the displayed
structural data; its source representation is arbitrary.

`pointInducedJacquet_repLength_eq_fullIntersectionCount` applies to actual
rational points, the actual standard parabolic and Levi family, and an
irreducible cuspidal source representation. The source and target subsets must
have equal cardinality. The explicit structural hypotheses comprise the
standard cocharacter and Levi-intersection theorems, actual relative roots,
normalizer and centralizer comparisons, finite actual Coxeter data with the
root-length comparison and exact standard-Levi Weyl identification, and
closedness of the actual Levis and unipotent radicals. The representation
carrier has universe `max (u + 1) v`, as in the imported geometric construction.

The intermediate theorem with suffix `_of_filtration` computes the length
from any supplied filtration of this exact type. The final theorem constructs
the actual ordered geometric object filtration with the
proved Haar epsilon cancellation. It retains its bijective enumeration of
all minimal Weyl representatives. Additivity expresses the induced Jacquet
length as the sum of its actual grade lengths. At a full source intersection,
equal source and target ranks make the geometric grade a conjugate of the
irreducible source, so it has length one. Every other grade is zero by source
cuspidality. The existing exact grade-length theorem proves both cases.
The finite indicator-count lemma then identifies the sum with the cardinality
of `fullIntersectionRepresentatives cs J I`.

The conclusion is an equality of actual representation lengths. It requires
no finite-length hypothesis on the induced representation and no irreducible
Jacquet detection premise. The latter is still needed to turn the family of
these Jacquet lengths into a bound on the induced representation itself.
