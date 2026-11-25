# Coherent restriction of actual subgroup images

This internal helper constructs restriction on all subgroup functors of the
actual pullbacks of a group scheme. For a morphism `a : T → M` over `S`,
`restrictImage a F` first pulls `F` back along `a.left` and then transports it
through the inverse of the actual direct/iterated pullback comparison.
`mem_restrictImage` gives its meaning on every relative scheme test.

The point adjunction `TorusSubgroupModuli.familyPointsEquiv`, despite its
namespace, is already defined for arbitrary group schemes and points. The
module reuses it and its projection theorem. The identity and composition
comparisons on relative tests have identity underlying scheme maps. Their
point identities prove `restrictImage_id` and `restrictImage_comp` by naturality
of the subgroup condition. Thus `subgroupPresheaf P` is an actual presheaf
with values in `Type (u+1)`, with all schemes in the original arbitrary
universe `u`.

`restrictImage_range` identifies restriction of a represented image with the
all-test image of the actual pulled-back inclusion and ambient comparison.
No choice of representative enters the restriction definition.

These are internal consequences of the published pullback and subgroup-functor
constructions. They provide coherence for the relative Levi moduli problem
in Conrad, *Reductive group schemes* (2014), Definition 5.4.2, p.174, registered
as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
This helper does not prove that a restricted Levi image is a Levi image:
stability of the unchanged relative-Levi predicate remains a separate
geometric obligation. It asserts no representability or torsor existence.
