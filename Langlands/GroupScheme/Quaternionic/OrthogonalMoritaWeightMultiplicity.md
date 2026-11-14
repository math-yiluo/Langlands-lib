# Character eigenbases and original division-algebra weight multiplicities

This internal derived helper connects a supplied character eigenbasis of an
actual split row representation with the original division-algebra cocharacter
weight spaces. It constructs neither a Morita comparison nor a character
eigenbasis. Its inputs retain these data and an equality of the actual
base-changed group-scheme morphisms.

`affinePointsBaseChangeMulEquiv_comp` proves naturality of the compatible affine
point base-change equivalence. The proof applies its inverse, uses naturality
of relative base-change points, and compares the underlying scheme morphisms.
`Gm.affineUnitsEquiv_baseChange` proves that the canonical base-change
isomorphism of the multiplicative group preserves the coefficient unit. It
uses naturality of the multiplicative-group point equivalence and the
canonical restriction-of-scalars isomorphism of the test scheme. These two
lemmas work over compatible towers of commutative rings.

`affinePointsBaseChangeMulEquiv_cocharacter` evaluates a base-changed
cocharacter by first base-changing the multiplicative point and then using
its canonical multiplicative-group identification. For a commutative group
scheme T over an integral domain, `characterWeights T chi nu` defines the
integer-valued family `i ↦ latticePairing T (chi i) nu`.
`affineUnitsEquiv_character_cocharacter`
identifies the value of a character on a cocharacter with the original
coefficient unit raised to the integer lattice pairing. The proof rewrites
the composite endomorphism of the multiplicative group as the integer
multiple of its identity.

In the namespace `Quaternionic.OrthogonalMorita`, `splitPoint_cocharacter`
evaluates a supplied equality between the actual base-changed cocharacter
followed by the Morita group isomorphism and a cocharacter of a commutative
group scheme followed by its split orthogonal representation. Naturality
and the preceding cocharacter formula give the equality on every compatible
coefficient point.

`weight_card_of_characterBasis` assumes fields K and L with an algebra
structure, a finite-dimensional division K-algebra D, a positive integer
degree with finrank_K D = degree squared, a supplied orthogonal Morita
comparison, and the preceding equality of actual group morphisms. It also
assumes a finite basis b of the split 2n-dimensional row module, indexed by I,
and characters chi_i of the commutative L-group scheme T. Its eigenvector
hypothesis holds over every commutative coefficient L-algebra and every
point of T: the inverse-right matrix action on b_i is multiplication by the
coefficient unit obtained by evaluating chi_i. For each cocharacter nu and
integer c, the conclusion is

    Nat.card {i // latticePairing T (chi i) nu = c}
      = degree * finrank D (sigma.cocharacterWeightSpace q f c).

The proof evaluates the character eigenlaw at nu on the compatible
base-changed multiplicative point. The point comparison and unit formulas
turn it into the actual split cocharacter eigenlaw.
`rowBasis_mem_of_split_eigen` then makes every pulled-back copy basis vector
homogeneous, with weights `characterWeights T chi nu`, for the actual extended
weight space.
`weight_card_of_rowBasis` counts that basis and cancels the positive degree
factor, giving the displayed equality in division-algebra dimensions.

The provenance is internal: these are deductions from the existing
base-change, lattice-pairing, actual row-action, weight-transport and
weight-basis APIs. There is no external existence assertion or restriction
on characteristic, field cardinality, or the universe u. The numbered
type-D character construction and its compatibility with the original
spin cover remain separate prerequisites of the host theorem.
