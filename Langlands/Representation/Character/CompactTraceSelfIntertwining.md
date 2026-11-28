# Self-intertwining from a translated compact trace test

Let \(K\) be a compact open subgroup of a Hausdorff topological group \(G\), and let
\(\tau\) be a finite-dimensional smooth complex representation of \(K\). The distribution
\(D\) is invariant under conjugation by \(G\). If \(D\) is nonzero on the character
of \(\tau\), translated to \(yK\) and extended by zero, then
`compactTraceSelfIntertwining` gives a nonzero intertwining map on \(K\cap yKy^{-1}\)
from \(a\mapsto\tau(a)\) to \(a\mapsto\tau(y^{-1}ay)\).

Insert an endomorphism \(B\) in the character test, using \(k\mapsto
\operatorname{tr}(B\tau(k))\) on \(K\). Evaluation after translating and extending by
zero defines a linear functional \(\Lambda(B)\). Conjugation by an element \(a\) of the
intersection preserves the coset. Writing \(b=y^{-1}ay\), cyclicity of the trace
gives \(\Lambda(\tau(a^{-1})B\tau(b))=\Lambda(B)\).
The trace pairing on endomorphisms identifies \(\Lambda\) with a map \(T\) by
\(\Lambda(B)=\operatorname{tr}(TB)\). The same trace pairing then gives
\(T\tau(a)=\tau(b)T\), and nonvanishing at \(B=1\) gives \(T\ne 0\).

This derives the self-intertwining step used in Clozel, *Characters of nonconnected,
reductive p-adic groups*, §3.7, p. 164. The test uses the ordinary trace and also
applies to reducible compact types.
