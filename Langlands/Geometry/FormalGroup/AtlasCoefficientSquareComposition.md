# Actual composition of commuting coefficient squares

`baseAlongSquareIso_comp` proves the whole integral atlas-map equation for
two adjacent commuting coefficient squares. It retains the specified actual
coefficient-equality maps, the actual coefficient-composition isomorphisms,
and their actual coefficient extensions. The composite outer coefficient
square is supplied with its true algebra-map equality; proof irrelevance
identifies it with the equality derived from the two smaller squares.

The implemented proof composes both routes with the same final direct
coefficient normalization and cancels that specified integral isomorphism.
The already proved three-map associativity equations, the actual two square
normalization equations, and the equality-transport composition equations
identify the two normalized routes. This establishes equality of whole
integral formal maps and uses their actual inverse equations.

Auxiliary lemmas prove actual supplied coefficient extension preserves
integral identity, composition and inversion, that equality transports compose,
and that equality in either supplied coefficient map gives its actual
composition square. The latter proofs eliminate the given map equality;
the square normalization equation cancels the actual target normalization.

`baseAlongSquareCompositionTestSquare` retains the two specified composite
formal maps on each test chart and the rationalization of their proved equality,
with actual integral identity maps at their common target.

The coefficient rings all have the same arbitrary universe, with the acting
ring and rational field in separate universes and arbitrary finite coordinate
types. Integral coherence needs no domain assumption; the rational test square
uses the existing domain/fraction-field hypotheses. Covers may be infinite and
coefficient maps may merge generators. This is internal coherence of existing
actual maps. Quotient-specialized composition and original framed composition
laws remain subsequent constructions; no representation theorem is assumed.
