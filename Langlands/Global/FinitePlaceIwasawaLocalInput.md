# Extracting finite-place Iwasawa data from local compact and product data

Author: Worker 1624.

This internal adapter connects the existing general local conclusion bodies
to the exact finite-place consumer. Its provenance is derived: it applies the
published unconditional field-extension proofs, extracts fields of the
published compactness and product predicates, and uses the actual point and
topology transport. It adds no structural assertion from the literature.

`SpecialCompact.IsCompactOpenMaximal.isLocalIwasawaCompact` works over a
field `F : Type u` with a topology and an actual affine group scheme `G`.
The topology on `rationalPoints G` is precisely the named
`rationalPointTopology F G.X`, bound locally. Given a subgroup `K`
satisfying `IsCompactOpenMaximal F K` and an actual group-scheme morphism
`j : P ⟶ G` with `PointProductEqualities (rationalPoints.map j).range K`,
it proves the existing `CoordinateCompactPatching.IsLocalIwasawaCompact`
predicate for that point homomorphism and the same subgroup `K`.

Compactness is the first field of `IsCompactOpenMaximal`. Its maximality
field ranges over all compact subgroups. For a compact supergroup `L`,
`Maximal.eq_of_le` gives `K = L`, whose reverse is the equality required
by the consumer. The first product field says that the whole point group
equals the parabolic image times `K`; reversing it gives the literal
source-left product equality required by the consumer. Openness and the
second product order are not needed for this deduction. There is no
valuation, local-field, reductivity or parabolicity premise in this
generic extraction.

For every number field `F : Type u`, actual connected reductive group
scheme `G` and finite place `v`, `baseChanged_isConnectedReductive`
applies `connectedReductiveFieldExtensionStatement` to the actual
extension `F → FiniteCompletion F v`. The conclusion concerns precisely
`baseChangedGroup F G v`. Similarly,
`baseChange_isParabolicSubgroup` applies
`parabolicFieldExtensionStatement` to every actual parabolic inclusion
`p : P ⟶ G`. Both imported theorems are unconditional proofs, and their
actual pullback maps agree definitionally with `Spec.algebraMap`.
Neither conclusion is supplied as an additional hypothesis.

`baseChangeIwasawaCompactOfParabolicProducts` takes one supplied subgroup
of rational points of this actual pullback, together with
`IsCompactOpenMaximal (FiniteCompletion F v)` and
`Iwasawa.AlgebraicParabolicProducts` for that same subgroup. It selects
the product for the actual base change of `p`, whose parabolicity has
just been proved. The generic extraction gives local Iwasawa compact
data on these rational points. `baseChangeIwasawaCompact` then maps the
subgroup by the actual continuous multiplicative point comparison and
transports compactness, unrestricted compact maximality, and the
literal product equality to `FinitePlaceGroupPoints F G v`.

All universes, carriers and evaluation topologies remain the published
ones. Here `FinitePlace F` is the height-one-prime index
`Langlands.Global.FinitePlace` used by the exact finite-place consumer.
No splitness, isotropy, standard-parabolic restriction or properness
restriction is imposed; in particular the improper parabolic remains
in scope.

The final construction is a function between subtypes of supplied
subgroup data. It constructs the image of that supplied subgroup but
proves no existence of an input subgroup. In particular, it does not
prove `FinitePlaceGroupPoints.ParabolicIwasawaStatement`. Existence of
one actual local subgroup with both compact maximality and products
for all actual algebraic parabolics remains the geometric prerequisite.
