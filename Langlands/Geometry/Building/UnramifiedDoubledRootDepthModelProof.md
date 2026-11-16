# Smooth doubled-root depth models for supplied apartment lifts

`Langlands.Geometry.Building.unramifiedDoubledRootDepthModel` proves exactly
`UnramifiedDoubledRootDepthModelStatement.{u}` for arbitrary universe `u`.
The supplied parahoric building, special torus, concrete unramified apartment
lift, point, root, closed root representative and nonnegative depth retain all
the published hypotheses. The comparison holds for every point over
`K = UnramifiedClosure F`, including points that do not extend an `F`-point.

This is an internal derived proof of the Library's source-free model interface.
Its inputs are the published fixed-point model construction, recovered integral
torus, integral split-root construction, torus-restricted root-fixer theorem and
root-character kernel theorem. It assumes no further model-existence or
comparison statement. The original statement and its imported files are
unchanged.

## Translating the depth

Write `c = 2a`. Since `c` is a root, it is nonzero. The split-torus evaluation
pairing supplies a real cocharacter vector `w` with `c(w) ≠ 0`; rescaling it
gives `v` with `c(v) = -s`. Translate the supplied upper apartment point
`L.e y` by the descended vector determined by `v`, obtaining `z`. The existing
Galois-equivariant descent-translation theorem and the supplied fixedness of
`L.e y` prove that `z` is coefficient-fixed.

`ApartmentLift.restrictedDepth_descentTranslate` proves that restricted depth
zero at `z` equals restricted depth `s` at `L.e y`. The definition takes suprema
over upper roots whose restriction is a positive integral multiple `m` of the
lower character. Evaluation on the descended vector is `-m*s`; the actual
root-filtration translation formula changes depth zero to depth `m*s`.
Equality at every term gives equality of the defining suprema. This argument
uses the actual apartment valuation supplied by `L`.

## The integral model and its generic fibre

`recoveredFixedPointModels` constructs compatible lower and upper full ambient
models for the coefficient-fixed point `z`, using already proved vertex,
bounded-model, intersection and unramified-descent constructions. The lower
full model is smooth. Its recovered lower apartment torus is an integral split
torus whose generic identification is the supplied lower torus. The helper
`IntegralTorusData.toFullIntegralSplitTorusData` composes its neutral-model
inclusion with the neutral-to-full inclusion; their generic commuting squares
supply compatibility in the full ambient model.

Apply `IntegralSplitTorusData.exists_model_of_rootRepresentative` to this full
model and the nonzero character `c`. The integral split-root construction gives
an integral root group, smooth with geometrically connected fibres, and a
closed inclusion into the ambient full model. Its generic fibre represents the
actual functor `RelativeRoot.subgroup P.i c`. The supplied `q : U ⟶ G`
represents the same functor, so uniqueness of representatives gives an
isomorphism from this generic root group to `U`, commuting with the inclusions
into `G`. Retarget the integral root model along that isomorphism. This is the
model `M` in the conclusion; its generic-fibre identification is the old one
followed by the representative isomorphism. Its integral group and inclusion
are retained. In particular, `M` is smooth and has geometrically connected
fibres. Base change to the residue field gives a geometrically connected
special fibre, hence the required connected special fibre. The commuting
isomorphism also produces a closed model map `φ` extending the supplied `q`.

## Exact comparison in both directions

Fix any `K`-point `x` of `U_K`, and put `g = q_K(x)`. Base change of the supplied
representability equality shows that `g` belongs to the actual lower root
subgroup over `K`. The supplied torus factorization identifies its inclusion
with the composite through the upper torus. The root-character kernel theorem
then puts `g` in the ambient character-valuation kernel.

The helper
`IntegralModel.hasIntegralCoordinates_iff_map_mem_baseChangeUnramified`, applied
to the closed map `φ`, identifies integral coordinates of `x` after the exact
`baseChangeCoeffEquiv` with ambient integrality of `g` in the base-changed lower
full model. This is an equivalence on all `K`-points: the closed-subgroup
integral-point criterion supplies the reverse implication as well as the
forward one. Recovery identifies these ambient integral points with those of
the upper full model, whose integral-point subgroup is exactly the intersection
of the character-valuation kernel and the point fixer of `z`.

Since `g` is already in the kernel, this intersection condition is equivalent
to fixing `z`. Since it is also in the actual lower root subgroup, the published
`restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero` identifies that
condition with restricted depth zero at `z`. Finally the translation lemma
identifies this with restricted depth `s` at `L.e y`. Every step is an equality
or equivalence, proving both directions of the target comparison without
restricting `x` or adding compatibility premises.
