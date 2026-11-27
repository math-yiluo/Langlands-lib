# Normalized product maps in the c-family

`cMapSourceTensor` and `cMapTargetTensor` identify the tensor of the two normalized inductions with the actual product induction for an inducing representation and its lower pullback. They use `normalizedProductInductionTensorEquiv`. The ambient Iwasawa factorization and the supplied lower Iwasawa factorization give compactness of their respective parabolic quotients. The affine finite-type rational point groups supply the local compactness and second countability for the product normalization.

`cMap_eq_tensor` expresses `cMap` using the two normalized product charts and the actual maps `cFactor` and `cDualFactor` on their joint convergence domain. The scalar is the inverse source gamma for the positive outer parabolic at the original compact subgroup. The proof unfolds `cMap` and identifies the two occurrences of each normalized product chart.

`cFamily_eq_transport` then applies `productInducedCoefficientTransport` along `twistPullbackEquiv`, identifying the lower pullback of the twist with the twist of the lower pullback. `cCompactFamily_eq_composite` records the ambient extension and lower restriction of this family via `productInducedCompactEquiv` on the two groups. Both identities follow by unfolding the corresponding definitions.

This decomposition uses the normalized product inductions in Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d’après Harish-Chandra*, V.1 and the proof of V.1.1, printed pp. 288–289, and the compact charts of IV.1, printed pp. 276–277. The source is registered as `waldspurger-2003-plancherel`, SHA-256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
