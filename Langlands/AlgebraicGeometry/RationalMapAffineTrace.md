# Detecting affine extension along a morphism at a factorial stalk

`rationalMap_mem_domain_of_affineTrace` starts with a partial map from `Y` to
`Z` over a separated base. The source `Y` is locally Noetherian and reduced,
and the target `Z` is separated and locally of finite type over the base.
Given `a : X ⟶ Y` and `x : X`, it tests the partial map at images under `a`
of the zero and principal prime points of the spectrum of the stalk at `x`.
Both stalks at `x` and `a x` are factorial domains. When the tested points
have values in one affine open of `Z`, the rational map is defined at `a x`.

The inverse image of that affine open within the partial map's domain gives
an open of the target stalk spectrum. The local ring homomorphism on the
stalks detects its zero and principal primes by
`FactorialAffineExtension.contains_primes_of_localMap`. The resulting
extension from the stalk spectrum spreads out to a neighbourhood of `a x`.
After taking an irreducible neighbourhood, agreement on the overlap with the
original partial map is checked at the generic point by separatedness and
reducedness. The two morphisms then glue to a representative on the union.
`rationalMap_extends_of_overlap` also records the restriction of the maximal
representative to a given compatible open.

This is a stalk form of the affine extension and restriction argument in
Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §4.4 Lemma 2 and the
proof of §4.4 Theorem 1, printed pp. 109–110 (PDF pp. 116–117). The literature
ID is `bosch-lutkebohmert-raynaud-1990-neron-models`, and the retained file
SHA-256 is `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
