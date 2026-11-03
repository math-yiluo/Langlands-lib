# The actual adjoint real cocharacter comparison

Authors: Worker 1334 and Worker 1475.

`adjointRealCocharacterComparison` proves the exact existing proposition
`Langlands.GroupScheme.AdjointRealCocharacterComparisonStatement.{u}`.
The universe `u` and field are arbitrary. The theorem uses the existing
`IsAdjointSplitTorusImage q i j p`, with its original group schemes,
maximal split tori, quotient square and fppf map `p`.

The proof is an internal composition of two focused comparison units.
`Rational.SplitTorusSurjection` proves real cocharacter surjectivity of
an actual fppf map of split tori. It cancels a scheme epimorphism to obtain
injectivity on integral characters, uses flatness of ℝ over ℤ, and applies
the published perfect real character/cocharacter pairing to deduce real
surjectivity. Its `cocharacterQuotientEquivOfFppf` constructs the resulting
first-isomorphism equivalence and proves its formula on quotient classes.

`Adjoint.RealCocharacterKernel` identifies the integral kernel of `p`
with the common annihilator of the actual relative roots. A cocharacter
is killed by `p` exactly when its composite into `G` is central on all
test schemes, by the quotient square and the full-centre kernel
criterion. The published `rootAnnihilatorCentrality` gives centrality
from integral root annihilation, and `root_restrict_eq_zero_of_isCentral`
gives the converse. Flat real scalar extension preserves this kernel,
and the published finite-character annihilator comparison identifies it
with `relativeCentralDirections i`.

The final proof obtains affineness of `G` from the given adjoint quotient
and the fppf instances from the given image data. It applies the proved
surjectivity and kernel equality, then transports the actual quotient
equivalence along that kernel equality. The Library's `TranslationSpace i`
is definitionally `V T / relativeCentralDirections i`. The transport's
quotient-class formula and the first-isomorphism formula give
`e (Submodule.Quotient.mk v) = cocharacterMapReal p v` for every `v`.

There is no additional comparison, rank, splitness-of-`G`, characteristic,
local-field, finite-kernel, integral-surjectivity or primitive-lift premise.
Rank zero and possibly nonsmooth centre are retained. All roots, real
spaces and morphisms are the existing Library objects. This internal proof
route uses the already published integral centrality theorem rather than
constructing the full root-lattice character comparison suggested in the
statement's source discussion.
