# Fpqc reflection of represented subgroup containment

This internal prerequisite is derived from the effective epimorphism theorem for
fpqc morphisms in Mathlib's `AlgebraicGeometry.Sites.Fpqc`. It supports the
all-test equality requirement of fixed-torus parabolic classification; it makes
no claim to prove that classification.

The exported construction `baseChangeOrderEmbedding` is the order embedding
from representable subgroup functors of \(G\) to subgroup functors of \(G_{S'}\)
given by base change. Its domain consists of pairs of a subgroup functor \(F\)
and a proof that some group-scheme monomorphism represents \(F\). The
representing group scheme and homomorphism are existentially quantified, so
different representations do not give distinct elements of this domain.

Let \(b:S'\to S\) be quasi-compact, flat and surjective. Let \(G\) be any group
scheme over \(S\), let \(F\) be any subgroup functor of \(G\), and let \(i:H\to G\)
be a homomorphism whose underlying morphism over \(S\) is a monomorphism.
Then \(F\leq\operatorname{range}(i)\) if and only if this containment holds after
base change along \(b\). Consequently, equality of subgroup functors represented
by monomorphisms can be checked after this base change. No smoothness, finite
type, reducedness, affineness, or field hypothesis is imposed.

The implemented proof first establishes factorization descent along any map
of test schemes whose underlying scheme map is an effective epimorphism.
Suppose \(x:U\to G\) factors through \(H\) after \(q:V\to U\).
The resulting map \(V\to H\) coequalizes the relations of \(q\), because its
composite with the monomorphism \(i\) does. `EffectiveEpi.desc` produces a map
of underlying schemes \(U\to H\). Cancellation against \(q\) proves that this
map is over \(S\), and that its composite with \(i\) is \(x\).

For fpqc reflection, the proof pulls back an arbitrary test scheme \(U\) along
\(b\). The projection to \(U\) is an effective epimorphism by Mathlib's fpqc
subcanonicality theorem. The base-change point equivalence and functoriality
of \(F\) supply the local factorization, which the preceding lemma descends.
Applying containment reflection in both directions proves equality reflection.
The tests \(U\) are arbitrary, including nonaffine and nonreduced schemes.

The declaration `baseChange_mono` also records the direct preservation of
containment for arbitrary subgroup functors under any base change.
