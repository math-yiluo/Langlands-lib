# Actual closed subgroup chains and simultaneous adelic height minima

Author: Worker 83.

This derived module constructs actual representations adapted to a descending
chain of closed subgroup schemes and proves that every finite prefix has
simultaneous adelic height minima at a rational right translate. It also
specializes the result to the canonical standard parabolics. The affine scalar
comparison, representation existence and subgroup inclusions are proved from
published Library results.

## Affine line stabilizers

For an actual matrix representation `ρ`, a test algebra `A`, an affine test
point `x`, and a coordinate index `j`,
`affine_coordinateLine_scalar_iff` identifies two conditions: the global-section
matrix sends `e_j` to a unit scalar multiple of itself; the actual `A`-coefficient
matrix does the same. It uses the canonical algebra equivalence
`Corepresented.affineSectionsAlgEquiv A`. In each direction, the proof maps the
unit through that equivalence, evaluates the vector equation coordinate by
coordinate, and uses the comparison `pointMatrix_eq_affineMatrix`. The column
entries and coordinate vector transport exactly. The result holds over any
commutative base ring and test algebra.

For a finite-type affine group scheme `G` over any field `k` and a closed
subgroup inclusion `z : H → G`, `Chevalley.exists_affine_line_stabilizer`
chooses a natural number `n`, an index `j : Fin (n+1)` and an actual
representation `ρ : G → GL_(n+1)` such that, over every test algebra `A`,
a point belongs to the actual range of `z` precisely when its affine matrix
acts on `e_j` by a unit of `A`. The proof imports the published all-scheme-test
theorem `Chevalley.exists_line_stabilizer` and applies the preceding
coordinate equivalence. This is a consequence of the stronger existing
all-test criterion, with no new geometric hypothesis.

## Descending closed subgroup chains

Let `F : Type u` be a number field and `G` an affine finite-type group scheme
over `F`. Specify actual group schemes `H i` and closed inclusions
`z i : H i → G` for natural indices `i`. Require their actual subgroup-functor
ranges to descend: if `i ≤ l`, the range of `z l` is contained in that of
`z i` on every scheme test.

`closedChainRationalSubgroup F G H z i` is the subgroup of actual rational
points of `G` given by that range on the affine test algebra `F`. Thus its
elements are points that factor through `z i` over `F`. It does not refer to
an abstract group model or to membership only after field extension.
`closedChainRationalSubgroup_antitone` evaluates the assumed all-test
inclusions on this rational test.

`exists_adapted_closedChain_minima` chooses dimensions `d i + 1`, coordinate
indices `j i` and actual representations `ρ i`. The line for `ρ i` has
stabilizer exactly the range of `z (i+1)` on every affine test algebra,
as in the preceding Chevalley criterion. These choices are independent of
the finite prefix length and of the adelic point.

For every finite length `r` and `g ∈ G(𝔸_F)¹`, there is a rational point `q`
in the range of `z 0` such that `h = g · rationalNormOne(q)` belongs to
`chainHeightMinimalSet` with constant one. Explicitly, for every `i < r`
and every rational point `s` in the range of `z i`,

`orbitHeight(ρ i, e_(j i), h) ≤ orbitHeight(ρ i, e_(j i), h · rational(s))`.

To prove this, choose each representation using the affine Chevalley theorem.
Each coordinate vector is nonzero by evaluation at its selected index.
For `i < l`, a rational point in the range of `z l` belongs to the range of
`z (i+1)` by descent, so its `ρ i` matrix scales that earlier vector by a
unit of `F`. This proves precisely the scalar premise of the published
finite-chain theorem in `AdelicHeightChain`. Apply that theorem and its
norm-one coverage corollary. The empty prefix is included. Neither reductivity
nor parabolicity is required for this general result.

## Canonical standard parabolics

`exists_adapted_standardParabolicChain_minima` assumes a connected reductive
`G`, a maximal split torus inclusion `i : T → G`, a generic cocharacter `ν`,
and a descending family `J l` of subsets of `simpleRelativeRoots i ν`.
It supplies the same simultaneous minima, where the minimizing group at `l`
is the actual rational subgroup of `standardParabolic i ν (J l)` and the
stabilizer of the chosen line is
`standardParabolic i ν (J (l+1))` on every affine test.

The proof uses the canonical `Standard.parabolicScheme` and
`Standard.parabolicHom`. Their closedness and range identifications are the
published `Standard.isClosedSubgroup_parabolicHom` and
`Standard.isRepresentedBy_parabolicHom`. The published proof
`standardParabolicOrder` turns the descending root subsets into descending
all-test parabolic ranges. The general closed-chain theorem then applies.
The final steps transport the rational subgroups through their exact range
equalities. No additional scalar-action or subgroup-nesting premise remains.
The result permits repeated subsets, nonsplit groups, and empty root sets.
It does not require a complete flag or assert that a supplied sequence is one.

## Provenance and remaining chamber obligations

This is a derived specialization of published actual Chevalley line
stabilizers, canonical affine section comparisons, the order on standard
parabolics, and the finite-chain height-minimum theorem. Springer (1994),
§1.2, printed p.208, supplies the context of representations adapted to
closed subgroups; §2.3, printed p.212, motivates the chain construction.
The formula's indexing concern is explained in `AdelicHeightChain.md`.
Here the representation at index `i` is explicitly adapted to the next
subgroup and is minimized over the preceding subgroup; the Lean theorem
does not claim a literal transcription of that displayed formula.

The module does not compare the adapted line characters with simple roots,
establish uniform root bounds, prove rank-one reduction, or convert minima
to the required positive torus and supplied compact subgroup. In particular,
it does not prove `AdelicSiegelChamberReductionStatement`.

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
Sci. (Math. Sci.) 104 (1994), 207–216. Registered source
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The cited original passages were read directly.
