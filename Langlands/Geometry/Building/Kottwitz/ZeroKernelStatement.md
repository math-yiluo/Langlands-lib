# KP Proposition 11.5.4: the zero subgroup

`Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement` states Proposition 11.5.4 of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed p. 431 (PDF p. 462). The November 2024 corrections do not change it. This is a Prop-valued statement awaiting proof.

For every nonarchimedean local field `F` and every connected reductive `F`-group `G`, the proposition quantifies over every actual maximal split torus inclusion `i : S → G`, minimal Levi inclusion `j : Z → G`, and Library datum `d : ZeroSubgroupDatum i j`. It asserts

`d.zeroSubgroup = ker (reductiveKottwitzRational F G hG)`.

`d.zeroSubgroup` is the Library's existing `G(F)^0` of KP Definition 2.6.23(3), built from the image of the simply connected derived cover and the zero subgroup of the minimal Levi. This file introduces no alternative definition. Quantifying over every datum also gives its independence of all choices once this proposition is proved. The statement does not assert existence of these data; it supplies the requested kernel equality for every datum defining the subgroup.

The Kottwitz map is the actual construction through normalized split-torus valuations, finite splitting-field norms, cocenters and z-extensions, followed by its unique invariant-valued rational restriction. No Kottwitz map or prescribed kernel is supplied as a hypothesis. There is no split, quasi-split, tame, rank, characteristic or residue-characteristic restriction. The valuation-kernel subgroup `G(F)^1` remains distinct and is handled by Lemma 11.5.2.
