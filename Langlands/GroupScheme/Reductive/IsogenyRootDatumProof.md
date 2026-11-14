# The actual root-datum comparison for split reductive isogenies

`Langlands.GroupScheme.isogenyRootDatum` proves the exact Library proposition
`Langlands.GroupScheme.IsogenyRootDatumStatement` in every universe. The
ambient field is arbitrary. The statement supplies connected reductive groups,
specified split maximal tori, actual finite reduced root data, and a finite,
flat, surjective ambient homomorphism commuting with the specified torus map.
The conclusion includes the torus isogeny, a characteristic-power root-datum
isogeny, both actual integral lattice-map identities, the full-kernel centrality
equivalence, and the isomorphism criterion with both centrality and bijectivity
of the entire weight map.

The proof first applies `IsIsogeny.isIsogeny_torusRestriction`. It chooses the
actual source-to-target root-index equivalence from
`IsRootDatumOf.isogenyRootIndexEquiv`, reverses it to orient the root-datum map
from target to source, and chooses the powers of `ringExpChar k` supplied by
its specification. These powers satisfy the exact integral root pullback
equations. The field characteristic exponent is one or prime.

`IsRootDatumOf.rootDatumIsogenyOfRootFactors` then constructs the root-datum
isogeny from these data. Its character map is actual pullback along the torus
map and its cocharacter map is actual pushforward. Injectivity and
transposition are proved on the entire integral lattices, including central
torus directions. The constructor derives the scaled coroot equations from
actual normalizer actions and finiteness of the target Weyl image. Its
specification gives both required actual-map identities.

When the constructed root-datum isogeny is central, every root factor equals
one. Its defining root equation therefore becomes exact pullback of the
corresponding target root to the source root.
`IsRootDatumOf.exists_rootParametrization_of_exactPullback` constructs an actual
source additive-line representative whose composite with the ambient map
represents the entire target root subgroup. This construction uses finite
schematic images and equivariance descent through the actual torus isogeny;
it does not assume that the original isogeny's differential is injective.

The comparison theorems in `IsogenyRootDatumKernelComparison` apply to these
representatives. Ordered root products make both opposite dynamic unipotent
kernels trivial on every scheme test. The generic opposite cell then factors
the entire ambient kernel through the source torus, and root annihilation
proves centrality of this full kernel. The established forward implication
gives the centrality equivalence. The self-centralizing maximal-torus
criterion and the character-lattice criterion give the isomorphism
equivalence, retaining its two conjuncts.

This proof assembles the imported geometric constructions and comparison
theorems; it introduces no additional mathematical assumptions. It proves the
lattice portion of Milne (2017), Definitions 23.1–23.2 and Proposition 23.5,
as specified in the unchanged target and its source discussion. The separate
root-coordinate polynomial formula is outside that target. Inseparable
isogenies, arbitrary central torus directions, and possibly nonsmooth kernels
are retained.
