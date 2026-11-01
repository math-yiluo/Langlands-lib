# Continuous actions on compact-open original-domain sections

## Provenance and inputs

This is an internal construction by Worker 56. It combines the actual
chosen-atlas action and whole-section transport from
`ChosenAtlasLocallyConstantAction` with the full function-space stabilizer
and discrete action constructions in
`Topology/GroupAction/CompactLocallyConstantStabilizer` and
`Topology/GroupAction/CompactLocallyConstantAction`. It attributes no new
assertion to external literature.

Let `K` be a complete ultrametric normed field and let `X` be a group action
in the category of chosen bounded affinoid atlas presentations. The group
`G` has its given topological-group topology. The additional continuity
hypothesis is exactly joint continuity of the original point operator
`(g,x) ↦ (X.ρ g).baseMap x`. Each group operator is already a full chosen
bounded atlas isomorphism, constructed as `X.ρAut g`; its base
homeomorphism is `isoHomeomorph (X.ρAut g)`.

The field, point, chart-index, coefficient and group universes are
independent. Coefficients form an arbitrary type `D`, without a topology,
action or nonemptiness hypothesis. All domains below are the actual
original-chart domains of this fixed atlas, with their original subspace
topologies.

## Full domain stabilizers

`ChosenAtlasSectionAction.domainStabilizer X S` is the entire setwise
stabilizer of the subset underlying `S` for the original point action.
`mem_domainStabilizer` identifies membership with the literal equality
`isoOriginalDomain (X.ρAut g) S = S`. It does not supply an invariance
condition as a separate input. This subgroup acts on the actual subtype
`S`, and `domain_smul_val` identifies its point operator with the original
base map. Each fixed operator is continuous because that base map is
continuous.

`continuous_domain_smul` restricts the original joint continuity to the
product of the subgroup and the domain, with their subspace topologies.
No compactness or openness is needed for this restriction.

If the actual subset `S` is compact and open,
`domainStabilizer_isOpen` proves that the entire subgroup is open in `G`.
The implemented proof applies compactness to the open preimage of `S`
under the joint point action, obtaining a neighborhood of `1` whose
elements send all of `S` into `S`. Continuity of inversion gives the same
condition for inverse elements. The two inclusions then give the exact
equality `g S = S`. Thus the subgroup contains a neighborhood of `1`,
which makes it open. `domainOpenStabilizer` packages precisely this full
subgroup as an open subgroup.

## Full functions on a fixed compact domain

For a compact original domain `S`, `domainLocallyConstantAction` constructs
an actual `ContAction` of its full setwise stabilizer on
`DiscreteLocallyConstant S D`. This wrapper contains every locally
constant function `S → D` and has the discrete topology. The group
operator is inverse precomposition:

`(g • f)(x) = f(g⁻¹ • x)`.

The restriction of joint point continuity and compactness allow the
imported compact function theorem to prove openness of every full
function stabilizer. The imported discrete-action criterion then gives
joint continuity on the entire function space. Openness of `S` is not
required for this relative action inside its setwise stabilizer.

`action_domain_section_pair` proves that this fixed-domain function
operator agrees with the earlier action on whole varying domain-section
pairs. For `g` in the setwise stabilizer and any full function `f`, the
actual pair operator sends `(S,f)` to `(S,g • f)`. Equality includes the
whole section and the exact domain; it follows from pair extensionality,
the stabilizer domain equation and point evaluation. This comparison is
algebraic and does not require a topology on `G`.

## Moving compact-open pairs and exact stabilizers

`CompactOpenOriginalDomainSection A D` stores an arbitrary
`OriginalDomainSection A D` together with proofs that its actual domain
subset is compact and open. These proofs do not select sections or alter
the original domain. The wrapper has the discrete topology and equality
is detected by the entire underlying pair.

`compactOpenMulAction` restricts the existing actual pair action to this
wrapper. The image domain is compact by continuity of the actual base
homeomorphism and open because that homeomorphism is open. Its identity
and composition laws are the existing whole-pair transport laws.
`compactOpen_smul_pair` exposes literal agreement with the existing
algebraic pair operator.

For any original-domain section `s`, even without compactness or
openness, `sectionStabilizer_eq_image` proves the exact set equality

`{g | X_section(g)(s) = s} = val '' Stab_H(f)`,

where `S = s.domain`, `H = domainStabilizer X S`, and `f` is the complete
function `s.value` with its discrete wrapper. If a group operator fixes
the whole pair, its domain equality puts it in `H`; the fixed-domain
comparison then gives equality of the full functions. Conversely,
fixedness of the full function in `H`, together with that same comparison,
fixes the whole pair. Both directions use the actual operators, and the
right side is the image of the full function stabilizer.

`compactOpen_stabilizer_isOpen` applies this equality to a compact-open
pair. Compactness and restricted joint continuity make the function
stabilizer open in `H`. Compactness and openness of `S` make `H` open in
`G`. The subtype inclusion of an open subset is an open map, so the exact
image above is open in `G`. Equality of wrapper pairs is equivalent to
equality of their underlying pairs, giving openness of the entire pair
stabilizer in the original group.

`continuous_compactOpen_smul` uses Mathlib's
`continuousSMul_iff_stabilizer_isOpen` to obtain joint continuity on the
full discrete wrapper. `compactOpenAction` packages this exact action as
`ContAction TopCat G`; its carrier is all compact-open original-domain
section pairs, and its operators are the original image-domain and
inverse-precomposition operators.

## Scope

The constructions retain empty domains and empty coefficient types when
the stated data exist. They require no default coefficient value, supplied
open pair stabilizer, section fixedness or output comparison.

Ambient openness is proved for compact-open original domains. Arbitrary
compact or distinguished domains need further geometric hypotheses for
such an ambient stabilizer conclusion. This module does not construct
all analytic domains, a general analytic or etale site, a general category
of smooth equivariant sheaves, or the Harris tower. It provides a concrete
continuous discrete section action for the stated local class of domains.
