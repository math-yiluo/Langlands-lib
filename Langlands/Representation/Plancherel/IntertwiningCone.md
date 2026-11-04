# Actual-root threshold regions for intertwining parameters

This is an internal construction on the Library's actual group-scheme
characters, subgroup supports and real torus spaces. It supplies parameter
regions and elementary comparison lemmas for a later application to
Waldspurger's intertwining theorem. It proves no convergence, rational
continuation or Plancherel theorem.

For a commutative group scheme `A` over an arbitrary field, an explicit real
bilinear form `B` on its entire real character space, a set of actual integral
characters `roots`, and a real threshold `R`, `rootThresholdRegion B roots R`
is the set of `x` satisfying `R < B x (1 ⊗ α)` for every indexed character
`α`. Increasing the threshold or enlarging the root set makes the region
smaller. The region for an empty root set is the entire real space. No
positivity or finiteness hypothesis is needed for these definitions and laws.
The term region is used because a nonzero threshold need not give a cone
closed under every positive dilation.

`rootThresholdRegion_nonempty_of_positivePairing` assumes that `A` is an
actual split torus, `B` is nondegenerate, and one integral cocharacter `ν`
has strictly positive integer pairing with every indexed character. It proves
that the real region is nonempty for every threshold. Splitness supplies
finite dimensionality of the full character space. The proof uses the inverse
of `B.toDual` on the functional pairing with `1 ⊗ ν`, obtaining a real vector
`x` whose `B`-pairing with `1 ⊗ α` is the integer lattice pairing of `α`
and `ν`. A positive integer is at least one; multiplying `x` by
`max (R + 1) 1` therefore gives every required strict inequality. This argument
needs no finite-set extrema. It includes the empty-root and rank-zero cases
and makes no assertion that this vector is realized by a point character.

For an actual morphism `i : A.toGrp ⟶ G` with affine `G`,
`intertwiningRegion` takes its indexing set to be
`intertwiningRelativeRoots i U Uop'`, the intersection of the nonzero actual
conjugation supports of the two supplied subgroup functors. Neither subgroup
is identified with an unspecified radical. Under smoothness of `G` and
splitness of `A`, the exact dynamic-support theorem gives the displayed
membership criterion when the subgroups are the actual positive dynamic
groups of `ν` and `-eta`: all actual roots with positive `ν`-pairing and
negative `eta`-pairing are retained, including multipliable roots. For
nondegenerate `B`, this real region is nonempty by the preceding argument.
No common-Levi or opposite-parabolic identification is required or asserted.

`invariantIntertwiningRegion` specializes to the Library's constructed
`relativeWeylInvariantForm i hA`. It retains the monomorphism hypothesis on
`i`, actual splitness, and an explicitly finite actual normalizer/centralizer
quotient. Its dynamic specialization is nonempty: strict positivity of the
form on every nonzero vector proves both separation conditions by testing
against the vector itself, so the nondegenerate-form result applies. The
form is on the entire character space, including central directions. This
specialization does not identify independently constructed forms for
different tori.

`CompatibleCharacterForms f B_A B_T L` is an explicit proposition about an
actual commutative group-scheme morphism `f : A ⟶ T`, the two specified forms,
and a specified real linear lift `L`. It requires that the actual real
restriction map `q` satisfy `q (L x) = x` and
`B_T (L x) y = B_A x (q y)`. It is a condition, not an existence theorem or
an assumed structural fact. From this condition,
`root_inequality_iff` transports an inequality on an ambient integral
character to the inequality on its actual restriction. The membership
comparison transports a whole region to the image of its root set under
actual character restriction. These proofs use the form identity and the
published pure-tensor formula for restriction. They claim neither that
restricted characters are nonzero roots nor that the condition holds for
arbitrary choices of the two forms. Constructing the appropriate ambient
form, lift and local metric remains an application obligation.

Over an arbitrary nonarchimedean local field, including positive
characteristic, `characterIntertwiningRegion` is the preimage of the real
region under `SplitTorus.normalizedRealPart` of an actual point character
restricted along an actual morphism `j : A.toGrp ⟶ M`. The membership lemma
expands precisely these inequalities. This uses the published normalized
parameter from the actual uniformizer section and perfect lattice pairing;
it does not substitute the raw natural-logarithm parameter. No smoothness,
unitarity or unramifiedness of an arbitrary point character is inferred.
`imageCharacterIntertwiningRegion` further pulls back along the published
actual valuation-image character construction for `M`. It does not replace
that image by a freely selected lattice or identify every real parameter
with such an image character.

The provenance is internal: actual subgroup-support comparisons, scalar
extension of the lattice pairing, finite-dimensional bilinear duality,
integer positivity and set preimages prove the results. The definitions are
intended for the strict all-root inequalities in Waldspurger IV.1.1, but no
source theorem is discharged here. The actual split component, common Levi,
opposite radicals, common ambient metric, realization by the required
unramified characters, and the analytic convergence and rationality
assertions remain separate obligations.
