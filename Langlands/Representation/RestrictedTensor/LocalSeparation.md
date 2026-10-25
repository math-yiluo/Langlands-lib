# Generic local separation of restricted tensor representations

This internal construction combines the published generic `RestrictedTensor.Action`
and `RestrictedTensor.Separation` interfaces. It introduces no external mathematical
claim. Its proof follows the elementary-tensor argument already implemented in
`Langlands.Global.FiniteAdelicGL.LocalTensorSeparation`, with the arithmetic data
replaced by arbitrary groups and subgroups. Its Library imports are only the generic modules; it also imports Mathlib's representation intertwining interface.

The coefficient field `K`, index type `ι`, family of groups `G i`, and family of
vector spaces `V i` have independent universes. The finite exceptional set is `E`.
The reference family `e` is fixed by `H i` outside `E`, and separation assumes it
is nonzero outside `E`. Its values inside `E` are arbitrary. There are no topology,
admissibility, finite-dimensionality, or spherical-Hecke assumptions.

`localInsertion H i` is Mathlib's `RestrictedProduct.mulSingleMonoidHom H i`,
viewed in the published `RestrictedGroup`. The laws `localInsertion_same` and
`localInsertion_of_ne` give its coordinates: the supplied group element at `i`
and the identity elsewhere. `localInsertion_injective` records injectivity.

`LocalTensorTail E i e` is exactly
`Space K (fun j : Outside {i} => V j) (tailSet {i} E) (fun j => e j)`.
The tail keeps all exceptional indices other than `i`.
`tensorLocalRepresentation` restricts the constructed representation along
`localInsertion`; `separatedLocalRepresentation` is `(ρ i).tprod` of the trivial
representation on this tail. Its action on a simple tensor changes only its
first factor, as stated in `separatedLocalRepresentation_tmul`.

`localSeparation_intertwines` proves equality of the two composite linear maps.
The proof uses `hom_ext_cofinal {i}` to consider stages containing `i`. The inserted
group element belongs to every reference subgroup outside that stage, so
`representation_pure_of_mem` computes its action on the same stage. Applying
`localSeparation_pure` on both sides isolates coordinate `i`. All remaining
coordinates are unchanged by the identity group element.

`localTensorSeparation` packages the published `localSeparation` and this law as
a genuine `Representation.Equiv`. `localTensorSeparation_pure` gives its finite
pure-tensor formula, and `tensorLocalRepresentation_reassemble` computes insertion
on the inverse image of any simple tensor using the inverse intertwining law.
`productLocalTensorSeparation` specializes directly to `productRepresentation`
and `ReferenceVectors`, using `family_nonzero`. The tail in this specialization
uses the restricted family `r.family`; the published `ReferenceVectors.tail_family`
identifies it with the family of `r.tail {i}`. Every construction is parameterized
by its own exceptional set, so applying it to two products imposes no equality
between their exceptional sets.

`stage_tprod_ne_zero` contracts a finite tensor using linear functionals taking
each specified nonzero vector to one. The induced scalar functional maps that
tensor to one, proving nonvanishing. This also handles the empty finite stage:
the empty scalar product is one. `space_nontrivial` chooses nonzero vectors only
at the stage `E`, forms their nonzero pure tensor, and applies the published
`of_injective`. It requires all local spaces to be nontrivial and nonzero
references only outside `E`, and applies to empty, finite, and infinite index
types. `product_nontrivial` specializes to `ReferenceVectors`.
`localTensorTail_nontrivial` applies the same theorem to `Outside {i}`; its proof
transfers the nonzero assumption using `mem_tailSet`. In particular it includes
an empty complementary index type.

These laws identify a local restriction with its local factor tensored with a
multiplicity space. They do not assert tensor-slice cancellation, uniqueness of
local factors, or existence of a factorization of an unrelated representation.
