# Open charts of closed torus subgroups tested on affine schemes

Author: Worker 1421.

This module defines a predicate `IsOpenChartOnAffines` and states one
proposition, `IsOpenChartOfAffinesStatement`, in namespace
`Langlands.GroupScheme.TorusSubgroupModuli`. It proves nothing.

## `IsOpenChartOnAffines j`

Let `S : Scheme.{u}`, `G : GroupScheme S`, `U : Over S`, `K : GroupScheme U.left`
and `j : K ⟶ (GroupScheme.baseChange U.hom).obj G`. `IsOpenChartOnAffines j` has
the same five fields as `TorusSubgroupModuli.IsOpenChart j`, with two of them
weakened:

- `isClosedSubgroup`, `isTorus` and `smooth` are unchanged;
- `injective` is required only for test objects `T : Over S` with
  `IsAffine T.left`;
- `isOpen` is required only for test objects `T` with `IsAffine T.left`. For
  such `T` and any actual closed torus inclusion `i : L ⟶ G_T`, it asks for an
  open `V` of `T.left` such that, for every `T'/S` with `IsAffine T'.left` and
  every `b : T' ⟶ T` over `S`, some `a : T' ⟶ U` satisfies
  `evaluate j a = evaluate i b` exactly when the image of `b.left` lies in `V`.

## `IsOpenChartOfAffinesStatement`

For every `S`, `G`, `U`, `K` and `j`, `IsOpenChartOnAffines j` implies
`IsOpenChart j`.

## Truth and intended proof

The proposition says that the open-chart property of the subgroup functor is
Zariski local on test schemes. It holds because evaluations are compatible
with composition (`TorusSubgroupModuli.evaluate_comp` in
`Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation`), membership in the
range of a closed immersion is local on the source, and morphisms to `U` glue
along open covers. The intended argument:

- For general `T`, cover `T.left` by affine opens `T_k` and take the opens
  `V_k` from the affine case. Applying the affine case to affine opens of
  `T_k ∩ T_l` shows that `V_k ∩ T_l = V_l ∩ T_k`. Let `V` be the union of the
  `V_k`.
- For `b : T' ⟶ T` with image in `V`, cover `T'` by affine opens mapping into
  the `V_k`. Obtain parameters on these pieces, glue them using injectivity on
  affine overlaps, and check the evaluation equality locally.
- Conversely, an evaluation equality restricts to affine opens of `T'` mapping
  into the `T_k`, so the image of `b` lies in `V`.
- Injectivity for general `T` follows from injectivity on an affine open cover.

This is a project-internal interface for the chart construction of task
`45ac6e52-a4d8-4414-91f1-03c3be35223e` (the torus case of SGA 3, Exposé XI,
Theorem 4.1, registered source `sga3-exposes-xi-xii-xiv-gille-polo-2008`). It is
not a literal statement of the source. Zariski locality of representable open
subfunctors is standard; compare Stacks Project, Tag 01JJ.
