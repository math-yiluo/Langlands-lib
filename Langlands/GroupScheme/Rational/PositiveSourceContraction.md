# Actual contraction from strictly positive intrinsic source weights

This is a derived construction using the published intrinsic split-torus weight
decomposition, cocharacter restriction, geometric Lie rigidity, equivariant
dynamic functoriality, and fpqc reflection of containment. It introduces no
structural existence premise implicitly and uses no additional literature.

Let `k` be any field in universe `u`, `T` a commutative group scheme, and `U` an
affine group scheme with an actual action `d` of `T`.
If `T` is split and `U` is locally of finite type, the theorem
`AutomorphicAction.positiveWeightSpan_eq_top_of_source_weights` says that strict
positivity of the pairing with a given integral cocharacter `ν` for every
character whose intrinsic source weight space is nonbottom implies that the
cocharacter-restricted action has full positive weight span. The condition
includes the zero character if its source weight space is nonbottom.

The proof uses the intrinsic split-torus decomposition to span the full Lie
algebra. Every nonbottom summand lies in the positive pairing semigroup by the
hypothesis. The published cocharacter restriction theorem identifies the span
of that semigroup with the positive integer weight span of the restricted action.

If `U` is also smooth and connected,
`AutomorphicAction.unipotent_eq_top_of_source_weights` says that its actual
identity-limit subgroup functor is the full source. This is an equality on all
test schemes. It applies the published geometric rigidity theorem: the smooth
closed identity-limit subgroup has full tangent image and hence equals the
smooth connected affine group. It does not infer group containment from Lie
containment without those geometric hypotheses.

Given any ambient group scheme `G`, a morphism `t : T → G`, a morphism
`i : U → G`, and all-test equivariance of `i` for `d` and conjugation along `t`,
`AutomorphicAction.range_le_unipotent_of_source_weights` places the full
pointwise range of `i` in the ambient dynamic identity-limit subgroup for
`ν` followed by `t`. Restrict equivariance along `ν`, use equivariant preservation
of identity limits, and then the full-source conclusion above.
This split-field theorem imposes no affineness condition on `G`, and neither
monicity of `i` nor a separate unipotence assumption on `U` is required.

For affine `G`, the theorem
`AutomorphicAction.range_le_unipotent_of_source_weights_baseChange` checks the
same strict positivity after any supplied field extension `K/k` over which `T`
is split. It uses the actual pulled-back action, all its intrinsic source weights,
and the actual base change of the specified cocharacter over `k`. No finite,
separable, or Galois condition on the extension is required. Connectedness
persists after extension for the smooth connected affine source. Equivariance
pulls back on actual points, so the split-field result gives containment over `K`.
Compatibility of dynamic identity-limit subgroups with base change transports
this to the original functors after extension. The field base map is fpqc;
the affine ambient dynamic subgroup is represented by a monomorphism, so
published fpqc reflection gives the all-test containment over `k`.

Finally, `positiveSourceFactorHom` is the actual morphism from `U` to any
supplied representative `j : V → G` of that dynamic identity-limit subgroup,
using the preceding extension criterion. Its theorem
`positiveSourceFactorHom_comp` says that its composite with this same `j` is
exactly the original `i`. The construction uses the published represented
subgroup factorization and does not select a different representative.

The local field-extension instances for affineness, smoothness, and connectedness
have explicit names prefixed by `positiveSourceContractionBaseChange`. These
names avoid collisions with generated instance declarations in other modules,
including `Torus.WeightBaseChange`, when the modules are imported together.
The instance bodies, mathematical declarations, and proofs are unchanged.

The supplied action, equivariance, splitting extension, and positive cocharacter
remain inputs. This module does not construct an initial positive direction,
prove a parabolic presentation, identify a supplied Levi centralizer, or prove
ambient maximal splitness. The host proposition
`MinimalParabolicLeviCentralizerStatement` remains a separate obligation.
