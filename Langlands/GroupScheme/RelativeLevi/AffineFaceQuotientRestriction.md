# Linear original vector quotients on arbitrary affine chart overlaps

Let two actual `AffineParabolicFaceChart`s present the same supplied relative
parabolic `p : H → G` of a reductive group scheme. Let `r : U → H` be its
supplied relative unipotent radical. Given arbitrary maps from `Spec A` to the
two chart bases, with equal composite map to the original base, this module
constructs and proves linear the comparison of the **original** coefficient
vector quotients. No etaleness of these new maps or nontriviality of `A` is
assumed. Both exact-layer ranks may vary or vanish.

`restrictionQuotientMap` is precisely the original `layerProjection` pulled
back along the specified affine map and followed by the canonical standard
vector coefficient isomorphism. `affineCoefficientIso` transports the existing
vector coefficient isomorphism along `Spec.map_preimage`; on a ring morphism it
equals that existing isomorphism. The restricted quotient has the full original
restricted next-term kernel and remains a full fppf quotient.

`restrictionTermIso` is induced by identity in the actual direct pullback of the
original ambient group. Equality of its represented ranges is proved by the
existing arbitrary common restriction theorem. Its ambient equation includes
the two specified original pullback tower comparisons. Monomorphism cancellation
proves compatibility with the original consecutive inclusions.
`restrictionQuotientIso` is the resulting actual full fppf quotient isomorphism.
Its factorization theorem retains exactly the two original restricted quotient
maps. The uniqueness theorem identifies every homomorphism with that same
original quotient square.

For linearity, a proved `RestrictionPresentation` compares each original
restriction with an actual full face model in the direct ambient pullback. Its
term, step and quotient squares and every-power scalar equivariance are all
constructed, using the coefficient-and-ambient adapter. Arbitrary affine maps
are treated by the induced algebra structure and transport of the entire
dependent assertion. The supporting coefficient model's stored maps, torus,
roots and assembled record are reducible aliases, exposing their existing
values for these dependent comparisons.

Over a nontrivial `A`, the prescribed parabolic representations and the
base-changed supplied radical derive equality of the two models' actual dynamic
parabolic and unipotent functors. The proved same-base canonical quotient
comparison is linear. Ambient monomorphism cancellation and full fppf quotient
uniqueness identify its square with the original restriction comparison.
Equivariance transfers through the two actual original-to-model quotient
isomorphisms. Over the zero ring every test over its empty spectrum is empty;
initial-scheme uniqueness proves the same actual equivariance equation.

The result commutes with every natural scalar power, has scalar weight one,
gives a linear equivalence over every coefficient algebra and equals one
base-ring matrix. That matrix formula holds on every scheme test. Neither
local term matching, scalar equivariance, transition linearity, a cocycle nor
descent effectivity is supplied as a premise. This is the concrete overlap
linearity input for the finite relative-radical filtration's vector-bundle
descent. The final global filtration assembly is a separate consumer.

This is derived internal infrastructure. The Lean proof uses represented
subgroup uniqueness, full fppf quotient uniqueness, the established unscaled
face comparisons and arbitrary-ring scalar rigidity. Larger finite elaboration
limits are confined to the coefficient helpers and the final scalar proof;
they do not change any mathematical assumption or kernel check.
