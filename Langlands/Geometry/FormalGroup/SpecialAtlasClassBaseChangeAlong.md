# Supplied-target extension and identity on special-atlas classes

This internal unit extends actual refined formal comparisons and their
special-atlas comparison classes along a supplied O_K-algebra map. It also
proves the identity law for special and height-certified comparison classes.

## Parameters and provenance

The parameters are exactly those of `SpecialAtlasBaseChangeAlong`: a
nonarchimedean local field K, a finite-dimensional central division K-algebra
D, and an embedded field `iota : L →ₐ[K] D`. Each input atlas supplies the
existing unramified full-degree integer-subfield certificate and geometric
tangent characters, with coordinates `Fin d` for d the reduced degree of D.
Existence of this subfield and the invariant 1/d specialization remain
separate.

R and S are arbitrary commutative O_K-algebras in the same universe v.
Principal covers may be infinite; complete families have universe v+1.
The geometric character condition retains its existing test-field universe
`max u v`, and L has its independent universe s. The coefficient map
`f : R →ₐ[O_K] S` need not be injective or flat.

This is an internal consequence of the existing actual formal comparisons,
special and height-certified quotients, coefficient extension, and
`AtlasOrderBaseChangeSelf`. It makes no new original-source assertion.
In particular, quotient equality is justified by constructed inverse formal
maps after refinement, and no representing object is assumed.

## Transport of refined formal comparisons

`reAlgebraComparison` transports a specified special-atlas `Comparison`
along equality of scalar algebra structures on the same ring. Equality
elimination retains the supplied two actual refinements, their common-cover
equality, and the full-order formal isomorphism with both inverse equations.
It does not choose a new comparison.

`reAlgebraComparison_onPoints` proves the square with the scalar-transport
linear equivalences on entire compatible families. After eliminating the
equality the square is reflexive. `equivalent_reAlgebra` therefore preserves
existence of an actual comparison. `IsoClass.reAlgebra` descends this operation
through the special-atlas comparison quotient; `reAlgebra_classOf` computes
its value on an actual representative.

`baseChangeAlongComparison g f` first applies the existing actual
coefficient extension of the refined formal comparison g and then transports
it along `coefficientAlgebraAlong_eq f`. Its source and target are exactly
the `baseChangeAlong` special atlases with the supplied scalar structure on S.

The equation `baseChangeAlongComparison_onPoints` is an equality of entire
division-order-module compatible families: extension followed by the
specified extended comparison agrees with the original comparison on the
restricted test followed by extension. Its proof composes the existing raw
coefficient-extension square with the scalar-transport square.
`baseChangeAlongComparison_fromPoints` gives the reverse square using inverse
family equivalences and that same specified formal comparison. It follows by
injectivity of the target family equivalence and its inverse laws.

`equivalent_baseChangeAlong` preserves the actual refined formal equivalence
relation. `IsoClass.baseChangeAlong` consequently descends extension to
special-atlas classes. `baseChangeAlong_classOf` is its representative formula.
No arbitrary comparison or representative is selected by this map.

## Identity coefficient extension

`baseIdIso X` is exactly `X.order.baseIdIso`. Its source is the actual
identity extension `X.baseChangeAlong (AlgHom.id O_K R)`, its target is X,
and its cover equality is `X.atlas.baseIdOpens_eq`. The imported construction
uses the actual basic identity-coordinate formal maps, proves commutation
with every division-order element, and retains both formal inverse equations.

`baseIdComparison X` places this formal isomorphism on reflexive refinements.
The right refinement is retargeted using the displayed cover equality.
Its coordinate isomorphism is the restriction of precisely `baseIdIso X`;
it is an actual refined formal comparison.
`classOf_baseChangeAlong_id` follows from this witness. Quotient induction
then proves `IsoClass.baseChangeAlong_id`: identity extension is the identity
function on special-atlas comparison classes. No definitional equality
between the original and identity-extended atlases is presumed.

## Classes with actual height certificates

`HeightSquaredAtlas.baseChangeAlong` extends each actual atlas together with
its original height certificate, using `SpecialAtlas.baseChangeAlong_height`.
The predicate requires irreducibility of pi in O_K, nilpotence of its actual
image in the base, and every original chart's actual scalar-kernel height
`d^2`, with the residue-field cardinality as q.
`val_baseChangeAlong` identifies the underlying special atlas exactly.
`equivalent_baseChangeAlong` uses the same actual refined formal comparison;
the two inputs already carry their own extended height certificates.

`HeightSquaredAtlas.IsoClass.baseChangeAlong` descends this operation within
the height-certified subtype. Its representative formula is
`baseChangeAlong_classOf`. `forgetHeight_baseChangeAlong` proves that
forgetting the certificate commutes with supplied-target extension, by
quotient induction and reflexivity.

`HeightSquaredAtlas.classOf_baseChangeAlong_id` uses the same constructed
`baseIdComparison` on the underlying atlas. Both representatives retain
their own height certificates. Quotient induction gives
`HeightSquaredAtlas.IsoClass.baseChangeAlong_id`.
No transfer of height to an uncertified representative is needed.

Successive supplied-map composition, a varying-base class functor and its
restriction to Nilp remain separate. These quotients classify the supplied
special formal atlases under actual refined formal comparison; the unit
does not construct framed triples, polarizations, actions, levels,
representing formal schemes or any representability theorem.
