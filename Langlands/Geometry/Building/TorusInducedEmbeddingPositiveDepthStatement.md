# Detection of positive character depths by an induced torus

`TorusInducedEmbeddingPositiveDepthStatement` is a proposition over a
nonarchimedean local field `F` in either characteristic. Its tori are over
`K = UnramifiedClosure F = inertiaFixedField F`. For each `K`-torus `T`, a
single closed immersion of `K`-group schemes `i : T ⟶ S` into an induced
torus `S` detects all positive real depths. For each `r > 0`, the preimage
of the standard subgroup `localTorusFiltration F S hS.isTorus r` under
`rationalPoints.map (CommGroupScheme.groupHom i)` is the normalized subgroup
`localGeometricCharacterCongruence F T r` of the full group `T(K)`.
The filtration on `S` uses its intrinsic affineness, supplied by
`SplittingAssembly.isAffine_of_isTorus`.

## Source and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See Lemma B.4.7 (printed pp. 662–663, PDF pp. 693–694), its use of the
Weil restriction adjunction in Fact A.3.20, and the proof of Proposition
B.10.1 (printed pp. 686–687, PDF pp. 717–718).

For a finite Galois splitting field `L/K`, the adjunction to the Weil
restriction of `T_L` gives a closed immersion into an induced torus. The
restriction of geometric characters to `T` is surjective. Since the standard
subgroup of an induced torus at positive depth is its geometric character
congruence, the preimage is the geometric character subgroup of `T`, denoted
`U_r` in the proof of B.10.1. The comparison concerns `U_r` before imposing
the depth-zero condition from the standard filtration of `T` in Definition
B.5.1. This is the comparison used with functoriality in Lemma B.10.4
(printed p. 687, PDF p. 718).
