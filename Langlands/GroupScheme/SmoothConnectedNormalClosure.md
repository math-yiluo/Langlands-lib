# Smooth connected normal closures and action stabilizers

This internal construction generates the closed subgroup envelope of the actual
map `(g,h) ↦ g j(h) g⁻¹`. Over any field `k : Type u`, the image of a homomorphism
between smooth connected affine group schemes has a smooth geometrically
connected affine closed normal closure. The homomorphism itself need not be a
closed immersion. No algebraic-closure or characteristic hypothesis is imposed.

## Actual normal closure

`SmoothConnectedNormalClosure j` extends `GeneratedImage` for
`SubgroupFunctor.conjugationMap j (𝟙 G)`. It stores the actual group and closed
inclusion supplied by that interface, together with:

- `HasSmoothConnectedGeneration`: smoothness, affineness, geometric
  connectedness, and a dominant positive product map from a finite power of the
  conjugation source;
- normality of the inclusion's range on every test scheme;
- containment of the original range of `j` in that range.

`exists_smoothConnectedNormalClosure` proves this type is inhabited when `G`
and `H` are smooth connected affine groups. The chosen construction
`smoothConnectedNormalClosure j` uses classical choice from that theorem.
There is no asserted canonical choice.

The proof uses `smoothConnectedAffineGeometry` to make `G.X ⊗ H.X` affine,
locally of finite type and geometrically integral. Its unit point `(1,1)` maps
to `1`. `ImageGeneration.pointedImageGeneration` therefore supplies the actual
smooth geometrically connected generated image. The conjugation map is
equivariant for left translation on its first factor and conjugation on `G`,
by `UnipotentAllBorelsEnvelope.conjugationMap_isEquivariant`.
`AutomorphicAction.closedImageEnvelope_isStable` makes its envelope stable
under conjugation on every test scheme; the representative consequently has
normal range. Substituting `(1,h)` into the source proves containment of `j`.

`SubgroupFunctor.containsImage_conjugationMap_of_isNormal` works over any base:
any normal subgroup functor containing the range of `j` contains its entire
conjugation image. It follows directly from the definition of normality and
the actual conjugation-map formula.

`SmoothConnectedNormalClosure.range_le_of_containsImage` places the normal
closure inside any supplied closed subgroup containing the full conjugation
image. It applies the generated image's minimality and the equivalence of
all-test image containment with actual morphism factorization.
`SmoothConnectedNormalClosure.range_le` specializes this to a closed normal
subgroup containing the original image of `j`. These conclusions concern
subgroup functors on all scheme tests, including nonreduced tests.

## Action and stabilizer application

The following two lemmas work over an arbitrary base.

`SchemeAction.kernel_le_stabilizer` puts the full all-refinement action kernel
in the stabilizer of every rational section. Evaluating its defining fixedness
condition at that section proves the inclusion.
`SchemeAction.containsImage_conjugationMap_stabilizer` then shows that every
conjugate of a trivially acting image lies in this stabilizer: the full kernel
is normal, so the preceding conjugation-image lemma applies.

Over any field, `SchemeAction.range_comp_le_kernel_of_dominant_orbit`
allows the dominant orbit to come from a different acting group `U` mapped to
the ambient group `G`. For `i : U ⟶ G`, `j : H ⟶ U`, and an action `a` of `G`
on `X`, assume:

- `H` is smooth and its range in `U` is normal;
- `X` is reduced, locally of finite type and separated over `k`;
- `H` fixes a supplied rational section `x` on all tests;
- the orbit map of `x` for `a.restrict i` is dominant and quasi-compact.

Then the range of `j ≫ i` lies in the full kernel of `a`. The proof first
applies `range_le_kernel_of_dominant_orbit` to the restricted action, then
expands restriction and composition on every test and every refinement. It
requires no smoothness, connectedness, affineness or closed-immersion condition
on `G`, `U`, `i` or `j` beyond the hypotheses just stated.

Finally, `SchemeAction.normalClosure_range_le_stabilizer` takes any
`D : SmoothConnectedNormalClosure j` whose original image lies in the full
kernel, and any supplied closed representative `b : B ⟶ G` of the stabilizer
of a rational section. The whole range of `D.inclusion` lies in the range of
`b`. It uses the full conjugation image and closed-envelope minimality.
Representability of the full action kernel is neither asserted nor assumed.

## Provenance and retained obligations

Worker 1547 implemented this internal generalization of the conjugate-envelope
argument in the published `Absolute.UnipotentAllBorelsEnvelope` module, whose
construction is attributed to Worker 1393 and compilation/documentation to
Worker 1461. Its public translation and equivariance declarations are reused
directly. The normality and original-image-containment proofs adapt that
published argument. Worker 317 proposed the normal-closure/stabilizer step in
the prescribed-Borel approach. The action application combines this
construction with the independently checked `SchemeActionDominantOrbit`
interface. No external structural theorem is assumed in the new proofs.

This module does not construct the dominant orbit or a proper Borel quotient,
prove the normal-solvable-torus theorem, establish a dimension-to-root
comparison, or prove `RankOnePositiveRootUniquenessStatement`. These remain
separate obligations of the parent task.
