# Positive-depth norm coverage for weakly induced tori

`WeaklyInducedTorusPositiveNormCoverageStatement` is a proposition over a
nonarchimedean local field `F` in either characteristic. Let
`K = UnramifiedClosure F = inertiaFixedField F`. For each `K`-torus `T`
satisfying `IsWeaklyInducedTorus F T` and each positive real depth `r`,
there exist an induced `K`-torus `S` and a `K`-homomorphism `n : S ⟶ T`
whose rational-point map takes `localTorusFiltration F S hS.isTorus r`
onto `localTorusFiltration F T hT r`. This is equality of the image subgroup
with the full standard subgroup of `T` at depth `r`. Both filtrations use the
affineness of tori supplied by `SplittingAssembly.isAffine_of_isTorus`.

## Source and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
See Definition B.6.2 (printed p. 669, PDF p. 700), Proposition B.6.6
(printed pp. 671–672, PDF pp. 702–703), and the admissibility argument
of Proposition B.10.5 (printed p. 687, PDF p. 718).

The witnesses in B.6.6 come from a finite tame Galois extension `L/K`
for which `T_L` is induced. Take `S = Res_{L/K}(T_L)`, which is induced
over `K`, and take `n` to be its torus norm to `T`. In B.6.6, the depth
`e(L/K) r` on `T(L)` uses the normalized valuation of `L`. The
filtrations on `S(K)` and `T(K)` both use depth `r` in the base field
normalization. The proposition records the resulting existential image
equality over `K`, with `IsWeaklyInducedTorus` as the only extra hypothesis
on the torus. The inclusion into the target subgroup is the functoriality
expressed by `map_localTorusFiltration_le`.
