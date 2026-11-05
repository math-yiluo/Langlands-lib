# Split products with a normal right factor

Author: Worker 60.

This derived construction works over every field `k : Type u`. Let `G` be
affine, and let `i : H → G` and `j : N → G` be closed subgroups with `H`
and `N` smooth, connected and split unipotent. Only `range j` is required
to be normal in `G`. For any smooth represented fppf-local product
`d : D → G`, `SplitNormalFactorProduct.isSplitUnipotent` proves that `D`
is split unipotent in the existing finite represented Ga-series sense.

The proof factors both inclusions through `d`. The lifted inclusion of
`N` is closed and normal in `D`, by cancellation of the monomorphism `d`.
The existing `SplitNormalFppfProduct.surjective_mulPoints` proves that
`N × H → D` is surjective. The existing split-series induction
`RelativeRoot.SplitSemidirect.isSplitUnipotent_of_surjective` then applies.
Its image hypothesis is discharged by the published
`SplitNormalFppfProduct.homImageHypothesis`. The argument does not require
`H` to be normal in `G`.

With the additional hypothesis that `G` is locally of finite type,
`SplitNormalFactorProduct.product` constructs a `Product i j` package.
The published smooth connected normal-factor product theorem supplies
the actual group scheme `D`, its closed inclusion `d`, its all-test
`IsFppfProduct` proof, smoothness and connectedness. The preceding criterion
gives split unipotence; `RelativeRoot.IsSplitUnipotent.isUnipotent` gives
unipotence in the existing coefficient-representation sense. The package
records these same actual objects and properties. It makes no additional
normality assertion about `D` in `G`.

The motivating source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The first paragraph of the proof of Corollary 2.2.5, printed p.64
(one-based PDF p.90), constructs the split smooth connected product
`U_G(λ) R_us,k(G)` using splitness under quotients (Proposition A.1.4).
The present general construction implements that product step by reusing
the Library's finite-series induction instead of forming a quotient of
`H` explicitly. It is an internal consequence of the published
normal-factor image and split-series APIs. The interpretation of a
product retains every relative scheme test and permits factorization
after an fppf cover. No rational-point surjectivity, local section,
perfectness, characteristic or infinitude assumption is added.
