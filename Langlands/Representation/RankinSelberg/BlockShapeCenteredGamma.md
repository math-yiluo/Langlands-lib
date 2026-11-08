# Gamma assembly on actual positive block shapes

This internal adapter preserves the actual positive block shapes, source actions,
canonical topology and self-dual measure. Its inputs are irreducibility,
admissibility and a nonzero entrywise Whittaker functional for each block.

`HasBlockShapeReflectedGammaData` records actual original and inverse-transpose
L-polynomial certificates for the two whole inductions and every mixed block
pair, the reflected-ratio datum, and the rational gamma expression for any
certified gamma factor of the whole pair.

`hasBlockShapeReflectedGammaData` eliminates each positive size function to a
successor-valued function, applies the existing two-family original and dual
L-polynomial constructions and the reflected-ratio theorem, and obtains the
whole rational gamma expression from the existing epsilon construction.
The supplied shapes and actions are retained through dependent elimination.
No exact equality of a whole L-polynomial and its block product is assumed.

`hasEntrywiseFunctional_smoothContragredient` handles arbitrary positive rank
by eliminating the rank to a successor. Genericity and multiplicity one give
Whittaker type; the existing standard/inverse character equivalence and the
actual smooth-dual transport then give a nonzero standard functional on the
smooth dual for the same supplied character. Rewriting the standard character
back gives the asserted entrywise functional. Irreducibility and admissibility
remain explicit inputs.

`centeredSegmentFamilyGammaGerm_of_blockShape` takes supplied square-integrable
segment parameters for a block family, real exponents, irreducibility and
admissibility of the untwisted blocks, a nonzero standard functional on their
whole twisted induction, and a certified gamma factor pairing that whole
induction with the normalized product of the actual smooth duals of its twisted
blocks. The second representation is precisely this product of block duals.
No identification with the smooth dual of the whole induction is claimed here.
The finite-product Whittaker criterion supplies each twisted block functional.
Twist invariance supplies admissibility and irreducibility, compact-open
cofinal duality supplies those properties for the smooth duals, and the preceding
functional theorem supplies their functionals. The block-shape construction now
gives the original and inverse-transpose mixed certificates and reflected ratio.
`centeredSegmentFamilyGammaGerm_of_reflectedRatio` yields the centered Appendix
gamma germ, using the negated character and the same underlying self-dual measure
for the inverse-transpose certificates. The existential epsilon coefficient is
nonzero and its exponent is integral.

`unitarySupercuspidalProduct_of_blockShapeGamma` additionally takes the actual
unitary generic datum, an equivalence from the original supplied action to that
whole twisted induction, its standard functional, the same mixed-product gamma
certificate, and the restriction that every positive real-axis order of its
rational spectral value occurs at zero. Positive ambient rank and the stored
block sum imply that the finite block family is nonempty. Square-integrability
gives block admissibility, and the supplied equivalence transports the
functional. The preceding germ theorem, Hermitian parameter symmetry, the
actual centered Euler bases, and the everywhere holomorphic nonzero epsilon
monomial give segment rigidity. The proved structural transport then gives
`IsUnitarySupercuspidalProduct` for the original action and the same block
shape, with an independently prescribed output block-carrier universe.

The provenance is internal composition of the imported constructions and
proofs. The segment-head and supercuspidal equal-rank factor statements remain
premises of both centered conclusions. This unit does not discharge unitary
generic exhaustion, construct the supplied segment parameters from arbitrary
blocks, identify the whole contragredient with the product of block duals,
establish the associated-pair gamma comparison or its real-order condition,
or prove the global associated supercuspidal induction statement.
