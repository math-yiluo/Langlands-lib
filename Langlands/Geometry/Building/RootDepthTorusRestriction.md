# Actual filtered root groups under restriction between split tori

This is an internal prerequisite for the actual building comparison. It starts
with an existing upper-torus root datum valuation and constructs canonical
filtered subgroups inside each actual lower-torus root group. It does not
construct an initial valuation, an apartment, or a building.

Let `k : Type u` be any field, let `G` be an affine group scheme over `k`, and
let `i : T.toGrp ⟶ G` be monomorphic. Retain an existing family `φ` and
`hφ : IsRootDatumValuation i φ`. Let `f : S ⟶ T` be a homomorphism of
commutative group schemes. The geometric comparison results below additionally
require smoothness of `G`, splitness of both tori, and a nonzero actual character
`α` of `S`. The ordered-product, exhaustion, and separation results also retain
the original upper hypothesis `RelativeRoot.HasOppositeFactorPairs i`.
No monomorphism of `f`, maximality of either torus, or building premise is used.

## Canonical filtration and auxiliary additive depths

For every real `r`, `torusRestrictedRootDepthSubgroup hφ f α r` is the supremum
of the actual subgroups `hφ.filtrationSubgroup χ (m * r)`, over actual upper roots
`χ` and positive natural numbers `m` satisfying `f ≫ χ = m • α`. This is a
subgroup of the original group `rationalPoints G`. Each factor consists of the
original upper root points with valuation at least `m * r`. The definition makes
no auxiliary cocharacter choice and no ordered-product assumption. The real
depth can be negative.

For a cocharacter `ν` of `S`, put `d = latticePairing S α ν`.
`torusRestrictionDepth f α ν r` is the additive homomorphism on the whole
upper character lattice given by

`χ ↦ (r / d) * latticePairing T χ (ν ≫ f)`.

Whenever `d ≠ 0` and `f ≫ χ = m • α`,
`torusRestrictionDepth_eq_mul` gives exactly `m * r`.
`latticePairing_comp_torusHom_of_restrict_eq_nsmul` proves the underlying
integer pairing equality `⟨χ,ν ≫ f⟩ = m * ⟨α,ν⟩`.
When `d > 0`, `latticePairing_pos_of_mem_torusRestriction` makes the transported
cocharacter positive on the entire positive restriction fibre.

`torusRestrictedRootDepthSubgroup_eq_selectedRootDepthSubgroup` identifies the
canonical subgroup with `selectedRootDepthSubgroup` for the actual character
semigroup `characterSemigroupPreimage f (cyclicTail α 1)` and this additive
depth. It needs only `d ≠ 0`. Consequently
`selectedRootDepthSubgroup_torusRestriction_independent` compares any two
auxiliary cocharacters with nonzero pairing; positivity is unnecessary for this
independence assertion.

`torusRestrictedRootDepthSubgroup_antitone` proves that increasing `r` decreases
the subgroup, directly from positivity of the natural multipliers and the upper
filtration's antitonicity. This property needs no splitness or opposite pairs.

## Exact actual-root comparison and coordinates

With smoothness, splitness of both tori, and `α ≠ 0`,
`torusRestrictedRootDepthSubgroup_le_rootGroupPoints` places every depth subgroup
inside the actual lower group `rootGroupPoints (groupHom f ≫ i) α`. This uses
the existing equality between that intrinsic lower root functor and the upper
selected semigroup subgroup. It does not need opposite factor pairs.

`exists_torusRestrictionRootDepth_enumeration` supplies an injective finite
upper character list `a : Fin n → characterLattice T` whose range is exactly the
roots indivisible within the selected semigroup, together with positive natural
multipliers `m j` satisfying `f ≫ a j = m j • α`. This enumeration result needs
smoothness and upper splitness, but neither upper opposite pairs nor the
monomorphism of `i`.

`orderedRootFiltrationProduct_eq_torusRestrictedRootDepthSubgroup` identifies
the ordered product of the actual upper filtrations at depths `m j * r` with
the canonical lower filtered subgroup, for every list with the specified exact
range and restriction equalities. The product equality permits repetitions and
the empty list. It follows that any two such lists give the same actual point
set, in any order. The multipliers and exact enumeration are available by the
preceding existence theorem; they are not an extra product premise.

For an injective list,
`mem_torusRestrictedRootDepthSubgroup_iff_existsUnique` gives exactly one tuple
of actual filtration points whose ordered product is a given filtered lower root
point. These theorems retain smoothness, both split tori, `α ≠ 0`, the existing
upper valuation, the monomorphic upper torus map, and the upper opposite pairs.
They do not assume lower valuation laws.

## Exhaustion and separation

`iSup_torusRestrictedRootDepthSubgroup` says that the supremum over all real
depths is the entire actual lower root group.
`mem_rootGroupPoints_iff_exists_torusRestrictedRootDepth` strengthens this to
pointwise exhaustion: every actual lower root point lies in some depth subgroup.

`iInf_torusRestrictedRootDepthSubgroup` says that the intersection over all real
depths is the identity subgroup. Thus the constructed descending filtration is
exhaustive and separated. These claims retain the same hypotheses as the
ordered-product theorem, including the existing upper valuation and opposite
factor pairs. No continuity or discreteness claim about the real depths is made.

## Implemented proof and provenance

This is a source-free internal derivation using existing Library objects and
lemmas. Naturality of the integer pairing is composition associativity; its
additivity gives the multiplier formula. Division by the nonzero pairing then
gives `m * r`. Reindexing the two subgroup suprema proves equality with the
selected additive-depth subgroup and removes the auxiliary choice.

For the geometric comparisons, the existing split-torus pairing theorem
`IsSplitTorus.exists_pairing_eq_pos` supplies a positive auxiliary cocharacter
for every nonzero `α`. The positive restriction multipliers make the whole
selected upper root set positive on its transport. The existing
`SelectedRootDepthCollection` product theorem and its actual coordinate
uniqueness theorem then apply. The restriction depth formula changes their
additive depths into `m j * r`. The existing actual semigroup/root-functor
equality gives containment in the lower root group.

For exhaustion, the existing actual lower root group is generated by all upper
root groups in the restriction fibre. Each of their points lies in some
multiplier-scaled depth subgroup: a finite upper valuation value `t` permits
depth `t / m`, and a top value permits depth zero. Antitonicity makes the family
directed under subgroup inclusion, so membership in its supremum means membership
at one depth.

For separation, use the existing unique intrinsic upper-root coordinates of an
actual lower root point. Membership at each depth supplies filtered coordinates;
intrinsic uniqueness identifies them with the same fixed tuple at every depth.
A nonidentity coordinate has a finite upper valuation `t`, contradicting the
bound at depth `(t + 1) / m`. Thus every coordinate is the identity, and so is
the original point. This proof uses the upper valuation's exact top-value law.

The construction proves no lower normalizer/reflection, commutator, double-root,
or opposite valuation law, no initial valuation existence, no geometric building
axiom, and no supplied-integral-model special point or unique fixation. The full
`BuildingComparisonStatement` remains unproved.
