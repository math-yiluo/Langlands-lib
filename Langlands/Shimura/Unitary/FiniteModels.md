# Concrete finite unitary models

Worker 1728. Derived local-model construction for Clozel 1991, Section 2,
printed pp.101–106, especially Lemma 2.2 and Proposition 2.3. It specializes
standard Hermitian matrix algebra to the actual completed quadratic center.

For a commutative R-algebra C with the specified R-linear involution,
matrixTranspose applies that involution to each entry and transposes. The
antidiagonal matrix J pairs coordinate i with n-1-i. Its square is the
identity, and its conjugate transpose is itself. maxWittAdjoint is the actual
adjoint J^{-1} conjugate-transpose(M) J, built using the existing adjoint
construction. These identities, the entry formula for matrixTranspose and
the zero pairings between the first floor(n/2) basis coordinates are proved
in Lean. This is the standard maximal-Witt Hermitian form: hyperbolic planes
and, in odd dimension, one middle line. No abstract Witt classification or
group-theoretic quasi-split equivalence theorem is claimed here.

At v of E the coefficient algebra is the actual E_v tensor_E K with its
constructed conjugation. IsQuasiSplitAt requires an E_v-algebra equivalence
from the actual E_v tensor_E A to matrices over that center. The equivalence
must carry the constructed center map to scalar matrices and intertwine the
actual extended involution with maxWittAdjoint. Thus the local condition
specifies the actual algebra with involution and its scalar structure.

SplitPlaceIdentification is an actual E_v-algebra equivalence from the
completed quadratic center to E_v times E_v, carrying conjugation to the
swap. IsSplitPlace is its nonempty existence proposition. It is arithmetic
split-center data, not a freely supplied label. IsDivisionAbove quantifies
local division over every actual K-place lying above v, so both conjugate
places are included when v splits. It does not suppose the involution fixes
an individual K-completion.

Source: Laurent Clozel, Représentations galoisiennes associées aux
représentations automorphes autoduales de GL(n), Publications mathématiques
de l'IHÉS 73 (1991), 97–145, Section 2, printed pp.101–106. Registered source
clozel-1991-selfdual-galois, SHA256
9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac.
The explicit antidiagonal presentation and tensor-center predicates are
derived constructions realizing the source's standard local unitary model;
the source's global existence assertion is a separate proposition.
