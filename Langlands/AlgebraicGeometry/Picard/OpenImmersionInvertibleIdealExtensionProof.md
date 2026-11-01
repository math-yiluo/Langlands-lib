# Extension of an actual invertible ideal

`openImmersionInvertibleIdealExtension` proves exactly the published
`OpenImmersionInvertibleIdealExtensionStatement.{u}` for arbitrary universe `u`,
without outer hypotheses. For a locally Noetherian scheme `X`, an open immersion
`j : Y ⟶ X` whose complementary structure-sheaf stalks are factorial, and a
monomorphism `s : D.obj ⟶ O_Y` from an actual line bundle, it constructs an actual
line bundle `E` on `X`, a monomorphism `t : E.obj ⟶ O_X`, and an actual pullback
isomorphism preserving the original inclusion.

The underlying module of `E` is `OpenImmersionIdeal.closure j s`, the pullback of
`j_*s` along the structure-module map `O_X ⟶ j_*O_Y`. Its map `t` is
`OpenImmersionIdeal.inclusion j s`, which is monic because `s` is monic.
The companion `OpenImmersionIdealSections` lemma identifies its image on each
open with the functions whose restriction lies in the image of `s`. The local
freeness theorem `OpenImmersionIdeal.isLocallyFreeRankOne_of_range_iff` then proves
that this module is locally free of rank one, using only the stated local
Noetherianity and factoriality outside the image of `j`.

The isomorphism `e` is `OpenImmersionIdeal.restrictionIso j s`. Its compatibility
`restrictionIso_hom_inclusion` gives exactly

```
(Scheme.Modules.pullback j).map t ≫
    (Langlands.Scheme.Modules.pullbackUnitIso j).hom = e.hom ≫ s.
```

The construction and proof impose no global integrality, reducedness,
connectedness, factoriality, separatedness, or quasi-compactness assumption. They
use no general line-bundle extension theorem or any of the valuative extension
conclusions excluded by the task. The geometric local-principality argument is
implemented in the local-freeness module; the present module performs the actual
sheaf construction and the final assembly. The original mathematical setting is
Stacks Project Lemma 31.29.2, Tag 0BD8, retained in the task's registered snapshot.
Worker 152 supplied the categorical closure, section lemma and final assembly;
Worker 303 supplied the local-freeness theorem.
