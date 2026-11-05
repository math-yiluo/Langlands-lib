# Shared morphism descent for adelic arithmetic models

This module contains the existing model-cone helpers extracted from
[`AdelicSpreadProperExistenceProof`](AdelicSpreadProperExistenceProof.md), with
identical definitions, statements and proofs in the reusable
`Langlands.AlgebraicGeometry.PointTopology.SpreadModelMorphisms` namespace.
It removes identical copies from the closed-immersion and functoriality proofs;
the topology-independence proof also reuses its cone projections. It adds no
new mathematical assertion.

For a diagram `D : I ⥤ Scheme`, a cone `c`, compatible maps to a scheme `B`,
and `X : Over B`, `modelConeLeg` is the actual projection between pullback
models, using pullback symmetry to put the factors in the usual model order.
`modelConeLeg_fst` and `modelConeLeg_snd` give its two projection identities.
`pullbackSymmetry_hom_hom` records the inverse symmetry identity.

When `I` is cofiltered, every `D.obj i` is affine and `c` is limiting,
`exists_modelMorphism` descends a prescribed morphism between pullbacks of
`X` and `Z`, retaining the exact cone square. It assumes that `X.hom` is
quasi-compact and quasi-separated and `Z.hom` is locally of finite presentation.
Its proof reuses `SchemeLimitModel.exists_level_morphism` and its cone identity;
it does not supply an additional descent premise.

`pullbackComp_snd`, `modelConeLeg_compIso`, `modelConeLeg_naturality` and
`pullbackComp_naturality` retain the canonical pullback-composition isomorphisms
and their projection or naturality identities. Their original hypotheses and
proofs are unchanged. The construction has an arbitrary common universe for
the diagram and schemes. Properness, closed-immersion, topology-independence
and continuity conclusions remain in their respective consumer modules.
