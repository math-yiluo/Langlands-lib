# Geometric connected components under base change

This is an internal supporting construction for the constructibility proof. It
compares the actual point-topology connected-component sets, including all empty
fibres, and derives transport of the exact component count in the host statement.
It does not assert constructibility.

## Homeomorphisms and algebraically closed field extensions

`GeometricComponentTransport.componentsEquiv` sends a component through a
homeomorphism by its continuous connected-component map. The corresponding map
for the inverse homeomorphism is its inverse: surjectivity of the point-to-component
quotient reduces both identities to the homeomorphism identities on points.

`algClosedBaseChangeEquiv` takes an algebraic space over an arbitrary scheme, an
etale geometrically surjective atlas whose structure map is locally of finite
type and quasi-compact, an algebraically closed field K with a map b to the base,
and a field extension represented by e : Spec L -> Spec K. For c = e followed
by b it constructs an equivalence between the actual components of `baseChange c X`
and `baseChange b X`. The iterated-base-change presheaf isomorphism identifies the
first fibre with the base change of the second. `RestrictionPoints.homeomorph`
identifies its point space with the represented product over Spec K.
`algebraicallyClosedAtlasComponentsEquiv` gives the component equivalence for
that product. The pulled-back chart remains locally of finite type and
quasi-compact because those properties are preserved by scheme base change.
All point topologies in these comparisons are explicitly `pointTopology`.

## Comparing geometric points over an ordinary point

`geometricPointFactorization` takes s : Spec L -> S with L algebraically closed
and an equality s(closedPoint L) = p. It returns a scheme morphism
Spec L -> Spec(AlgebraicClosure(kappa(p))) whose composite with
`componentCountGeometricPoint p` is s. After eliminating the equality, the
residue-field homomorphism into L comes from `Scheme.stalkClosedPointTo s` and
`Scheme.descResidueField`. With the algebra structure induced by that homomorphism,
Mathlib's `IsAlgClosed.lift` embeds the algebraic closure into L. The algebra-hom
commutation equation and the residue-field factorization theorem prove the
required scheme-morphism equation. No algebraicity assumption on L/kappa(p) is
needed.

`geometricFibreEquiv` applies this factorization and
`algClosedBaseChangeEquiv`, with K the algebraic closure of kappa(p). The two
`baseChangePointsHomeomorph` comparisons give the endpoints as the represented
products over S used in the host component-count definition. Its hypotheses
are the given locally finite-type quasi-compact etale surjective atlas and the
specified algebraically closed point over p.

## Arbitrary base morphisms and the exact count

`baseChangeGeometricFibreEquiv` takes any scheme morphism g : T -> S and q in T.
The geometric point b at q followed by g lies over g(q), since the residue-field
point map has constant value q. Iterated base change and the cross-base point
homeomorphisms compare the geometric fibre of `baseChange g X` at q to the
represented-product fibre of X at b followed by g. `geometricFibreEquiv` then
compares it to the canonical geometric fibre at g(q). Thus the conclusion is an
equivalence of actual connected-component sets with their prescribed topologies.
There is no quasi-separatedness, Noetherian, or finiteness hypothesis on g or
either base; the atlas finiteness assumptions remain explicit.

`geometricFibreComponentCount_baseChange` specializes to arbitrary affine bases
Spec A and Spec B and any morphism between them. It obtains the atlas from
`FinitePresentationOverRing B X` and applies `ENat.card_congr` to the constructed
equivalence. Consequently the exact host count at q after base change equals the
original exact host count at g(q), for every q. Quasi-separatedness is not needed.

The provenance is the explicit composition of the Library's point-topology,
atlas-component and base-change constructions with Mathlib's residue-field and
algebraic-closure maps. This is internally derived content, rather than a
transcription of a separate literature statement. Generic splitting and descent,
Noetherian induction, and arbitrary-ring approximation remain obligations for
the unrestricted constructibility theorem.
