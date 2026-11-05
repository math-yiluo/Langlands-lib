# Actual joint detection of Cartan parameters

This internal derived module specializes `JointCartanDetection` to the actual
simple-root pairings and the ambient rational-character valuation of the
published uniformizer powers. It uses existing Library constructions and
introduces no new assertion from the literature.

The imported `Plancherel.RenardCartan.rationalCharacterValuation_map_uniformizerSection`
identifies each ambient
valuation coordinate with the pairing of the cocharacter against the actual
restricted group character. It follows from functoriality of character
valuation and the intrinsic uniformizer evaluation formula.

`rationalCartanJointDetection` assumes connected reductivity, an actual maximal
split torus, a generic cocharacter, and the relative-root-system realization,
as in the host compact-restriction statement. Equality of simple-root pairings
implies equality of rational cocharacter evaluation on the full relative-root
span: negation stability of the roots and genericity give generation by the
simple roots. Equality of ambient valuations gives equality on all restricted
group characters. The published theorem that roots and restricted rational
characters span then gives equality on the entire rationalized character
lattice. The integral perfect pairing for the actual split torus identifies
the cocharacters. This needs only joint spanning; it assumes no complementary
subspaces or additional central-direction theorem.

There is no nonempty-root or positive-rank premise. In relative rank zero, the
restricted-character directions still span everything required for detection.
This unit establishes structural detection only; coefficient bounds from
cuspidality and the full compact-restriction theorem remain separate.
