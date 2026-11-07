# Coordinate invariance from the simple roots of a chamber

This is derived supporting work by Worker 1369. It combines actual smooth
root-subgroup representatives, the closed coordinate stabilizer envelope and
the Library's simple-root generation theorem. It makes no new assertion from
external literature.

Let `k` be an algebraically closed field of arbitrary universe `u`, and let
`U` be an affine smooth group scheme over `Spec k`. For an actual coordinate
`b : AffineCoordinates.algebra U`, the previously constructed
`CoordinateTranslationClosure.leftStabilizerEnvelope U b` is a smooth closed
subgroup `E` of `U`. The underlying scheme image of its inclusion `E ⟶ U`
is the Zariski closure of the locations of rational translations preserving
`b`, and its translations preserve `b` on every relative test scheme.

Given an affine ambient group scheme `G` and a homomorphism `j : U ⟶ G`,
`ambientStabilizerHom j b` is the actual composite `E ⟶ U ⟶ G`. This
definition by itself does not assert that the composite is a closed inclusion.

`factorsThrough_stabilizerEnvelope` takes a smooth scheme `P` over `Spec k`
and an actual morphism `a : P ⟶ U.X`. Its premise says that, for every
rational point `h` of `P` and every rational point `g` of `U`, evaluation
of `b` at `(h ≫ a) * g` equals evaluation at `g`. The theorem constructs
a factorization of `a` through `E`. Smoothness makes `P` reduced and locally
of finite type. The rational-density lemma puts the range of `a` in the
closure of the rational stabilizer locations, which is exactly the range of
the closed envelope. The closed-factorization lemma then supplies the
actual morphism through `E`.

For the remaining results, also assume `G` is smooth and connected and supply
`hG : IsConnectedReductive G`, a split maximal torus `i : T.toGrp ⟶ G`,
an actual root datum `Q` for this inclusion, and a generic cocharacter `ν`.
The group `U`, with the closed inclusion `j`, must represent exactly
`Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)`. These are hypotheses,
not existence conclusions.

`mem_range_stabilizerEnvelope_of_simpleRoots` assumes the following rational
simple-root invariance: for every `a ∈ simpleRelativeRoots i ν` and rational
points `x,g` of `U` such that `x ≫ j.hom.hom` belongs to the actual relative
root subgroup for `a`, the evaluations of `b` at `x * g` and `g` agree.
For every relative test scheme `V` and every `x : V ⟶ U.X`, the conclusion
places `x` in the image of the actual inclusion `E ⟶ U`.

The proof chooses the published smooth closed representative of each simple
relative root subgroup. Positivity embeds this representative in `U`, using
the represented-subgroup inclusion morphism. The rational invariance premise
and the preceding factorization lemma put its image in `E`. Thus the closed
subgroup `E ⟶ G` contains all simple relative root subgroups. The published
`LeviGluing.unipotent_le_range_of_simpleRoots` puts the full chamber
unipotent subgroup in its image on every test. Monicity of `U ⟶ G`
cancels the ambient inclusion and gives the claimed image membership in `U`.

`leftInvariant_of_simpleRoots` combines this membership with the envelope's
all-test invariance to prove `b(x * g) = b(g)` for arbitrary `V` and arbitrary
`U`-valued points `x,g` of `V`. Here the notation means the actual
`AffineCoordinates.pointAlgebraHom` evaluations in the coordinate algebra of
`V`. Taking `g = 1`, `eq_identityValue_of_simpleRoots` identifies evaluation
at every `x` with the evaluation at the identity point of the same test.
No reducedness, affineness or nonemptiness condition is imposed on `V`.

The rational simple-root premise is retained. This unit does not establish
that premise for a Steinberg covariant, the fixed-height restriction injection,
the dimension of the whole induced space, or `SteinbergBigCellStatement`.
