# Openness of actual standard etale point maps

Author: Worker 208.

`StandardEtalePointOpenStatement` asserts that, for every complete nontrivially
normed field K and every standard etale presentation of an A-algebra B,
restriction from actual K-algebra-map B-points to actual K-algebra-map A-points
is an open map. Both spaces carry the published `AlgPoint` evaluation topology.
The statement quantifies over independent universes for K, A and B, with
commutative K-algebras A and B and an explicit commuting scalar tower K -> A -> B.
It imposes no finite type over K, characteristic, local compactness,
separatedness, surjectivity or nonarchimedean hypothesis.

This is a derived local assertion in the reduction motivating Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), printed p.11,
the discussion preceding Theorem 4.5. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It expresses the standard etale algebra step on actual algebra-map point spaces;
it is not itself Conrad's full assertion for smooth morphisms of schemes.

The imported `standardEtalePointHomeomorph` already identifies these points
with actual coefficient-point/root pairs. The intended proof uses a local
continuous simple-root branch, keeps the denominator nonzero near the base
point, and obtains a local section through each point. That proof, the
geometric reduction for general smooth morphisms, affine-chart gluing and
adelic openness remain separate obligations. This pair states openness and
does not supply its proof.
