# The equivariant étale base-change morphism of sites

For a morphism \(f:Y\to X\) of spaces with operators over a fixed complete
nonarchimedean field, `equivariantEtaleBaseChangeMorphism` proves that
`etalePullbackFunctor f` is representably flat and continuous for the
equivariant étale Grothendieck topologies. The functor restricts the action
along the group homomorphism of \(f\) and takes the analytic pullback along
its underlying map.

For a site arrow \(g:U\to V\), `etalePullbackMap_isPullback` proves that the
square formed by its base-changed arrow and the projections to \(U\) and
\(V\) is an analytic pullback. The pullback lift defining the new arrow
makes the projections commute with \(g\). The compatibility of each arrow
with its structure map identifies the outer rectangle with the base-change
square for \(U\). Cancelling the base-change square for \(V\) yields the
desired square.

Pasting these projection squares around a cospan shows that the functor
preserves its analytic pullback. The terminal object has identity
structure map, whose pullback is an isomorphism. The Library's
finite-limit criterion gives representable flatness from preservation of
pullbacks and the terminal object.

For any point of a base-changed target, joint surjectivity supplies a point
in some covering source over its image in the original target. The
covering arrow is étale, so the point-lifting lemma for analytic pullbacks
lifts this pair to a point in the base-changed covering source. The images
of the generating covering families are therefore jointly surjective,
which gives continuity by the Library's criterion for the generated
Grothendieck topologies.

V. G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
unfinished manuscript (1995–1996), §1.2, printed/PDF p. 3, gives the site
morphism and its base-change formula. Literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
