# Associated normalized Jacquet transport and conditional unitary support

This derived supporting construction retains the original point-root
comparisons and the standard-cocharacter premise of the rational
self-association target. It uses the canonical ambient `pointTopology`.
The field universe `u` and representation carrier universe `v` are independent.
Every finite simple-root subset, specified point-normalizer lift of its
`longestRep`, and standard cocharacter for that subset is allowed.
The underlying group is a connected reductive group over a nonarchimedean
local field with its actual maximal split torus and generic cocharacter;
local compactness, nonarchimedean structure and standard radical closedness
remain explicit.

`associatedOppositeJacquetIso` constructs a natural isomorphism between
normalized opposite Jacquet restriction followed by Levi conjugation and
associated standard Jacquet restriction. The source Levi is the literal
original standard Levi, and the target Levi is the literal associated
standard Levi. The pullback homomorphism sends a target Levi element `m`
to `n * m * n⁻¹`, where `n` is the specified lift.

The construction applies the generic `jacquetConjugationIso` at `g = n⁻¹`.
Its Levi and radical membership hypotheses come from
`associatedOpposite_mem_of_pointRootSigns`. The standard and opposite
semidirect decompositions and opposite radical closedness are the published
actual constructions. The generic isomorphism proves compatibility of the
actual Haar half-normalizing characters under this conjugation and checks
equivariance on coinvariant generators. Its naturality follows from the
intertwining property of every smooth representation morphism.
`associatedOppositeJacquetIso_hom_mk` records the resulting formula
`[a] ↦ [A(n⁻¹)a]`. Thus the construction upgrades the earlier carrier
equivalence to an isomorphism of representations after the stated pullback.
This construction requires no reciprocal-character premise.

The three unitary-support consequences additionally retain
`RationalOppositeHaarReciprocityStatement`, Hausdorffness of the ambient
point group, and admissibility of the smooth representation.
`unitary_jacquet_subsingleton_iff_associated` proves equivalent vanishing
of the original and associated normalized standard Jacquet modules when
the representation is unitarizable. It obtains a common Levi-central
contracting element and its actual opposite Iwahori contraction basis from
`rationalOppositeIwahoriBasisStatement`; no basis is supplied as a premise.
The retained Haar statement supplies reciprocity on the full common
literal Levi. The proof then composes
`unitary_jacquet_subsingleton_iff_opposite` with
`associatedOppositeJacquet_subsingleton_iff`.

The first equivalence uses the actual Hermitian identification arising
from an invariant positive form and the proved normalized opposite Jacquet
duality from stable Iwahori pairings under the displayed contraction and
reciprocity data. The second equivalence is the earlier actual carrier
translation. No admissibility of either Jacquet module is assumed.

`not_isUnitarizable_of_associatedJacquet_asymmetry` and
`not_isUnitarizable_of_associatedJacquet_reverse_asymmetry` apply the two
directions: if either actual standard Jacquet carrier is nontrivial and
the other is a singleton, admissibility rules out an invariant positive
form under the retained Haar premise.

This pair neither proves the retained Haar statement nor establishes
admissibility, unitarizability or support asymmetry for a particular
representation. It assumes neither irreducibility nor finite length and
adds no maximal-proper-subset or nonempty-root requirement. All assertions
are derived from the named published subgroup transport, functor
conjugation, contraction-basis and unitary-duality constructions; there is
no new literature assertion. The dependency route uses no classification,
character independence, geometric lemma, adjointness or cuspidal-support
theorem. It does not prove `RationalRankOneSelfAssociationStatement`.

The 1 local instance has module-specific names to prevent generated-name
collisions when related modules are imported together. The instance types,
bodies and local scope are unchanged.
