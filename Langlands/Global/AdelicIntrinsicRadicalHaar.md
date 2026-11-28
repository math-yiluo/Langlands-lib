# The intrinsic radical and its normalized Haar measure

For \(P_I\subseteq P_Q\), `NestedRadicalSplit` gives a complement \(W\)
to \(N_Q\) in \(N_I\), with a map \(W\to M_Q\). Its image is the preimage
of \(N_I\) in \(M_Q\). To prove the reverse inclusion on each test
scheme, take an element of the intersection, decompose it in
`NestedRadicalSplit`, and apply the Levi retraction of \(P_Q\). The
retraction kills the \(N_Q\) factor and fixes the \(M_Q\) factor. The
intrinsic standard family identifies this preimage with the radical of
its parabolic indexed by \(I\). Uniqueness of represented subgroups gives
the group scheme isomorphism over \(M_Q\).

`IntrinsicRadicalHaarStatement` transports the isomorphism to the actual
adelic subgroup ranges. It intertwines their ambient embeddings and
identifies their principal lattices by naturality of rational points.
Push forward an initial Haar measure along this isomorphism. The induced
map of discrete quotients preserves the quotient measures, so the masses
of the respective fundamental domains agree. Dividing by those masses
and using independence of the initial Haar choice gives the exact
pushforward of the normalized ambient measures.

This identifies the inner radical factor of the successive Iwasawa
integrations in the face decomposition (7.26) with the quotient
normalization used in (7.23).

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 28–30, (7.23) and (7.26).
