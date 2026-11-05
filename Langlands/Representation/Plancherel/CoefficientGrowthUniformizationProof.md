# Uniform coefficient degrees from finite generation

Author: Worker 1564.

`Langlands.Plancherel.finiteLengthCoefficientGrowthUniformization` proves
`FiniteLengthCoefficientGrowthUniformizationStatement.{uG,uV}`. For a
topological group with compact-open cofinality, an admissible finite-length
smooth complex representation, and a submultiplicative real height bounded
below by one, coefficientwise polynomial growth implies one natural exponent
for every vector and smooth functional. Constants remain coefficient-dependent.
The group and carrier universes are independent.

The private `powerBound` predicate supplies a positive real constant for an
all-group power bound. Its elementary lemmas establish closure under addition
and complex scalar multiplication, monotonicity in the degree, and closure
under left and right translation. For a translate by `h`, submultiplicativity
absorbs `H(h)^d` into the positive constant. The bound `H ≥ 1` makes degrees
monotone and guarantees positive translation constants. No continuity,
symmetry, properness, or normalization at the identity is used.

For a fixed vector, `dualDegreeSubrepresentation` consists of smooth dual
functionals with a degree-`d` bound. The actual contragredient action translates
the coefficient on the left by the inverse group element, so this is a
subrepresentation. Its associated complex group-algebra submodules form an
ascending chain. The coefficientwise premise exhausts the smooth dual.
`exists_top_of_exhaustive_chain` applies Mathlib's
`Submodule.FG.stabilizes_of_iSup_eq` to show one member is the whole module.
Thus each vector has one degree valid for every smooth functional.

`vectorDegreeSubrepresentation` consists of vectors whose coefficients with all
smooth functionals have a degree-`d` bound. Right translation proves group
invariance. These submodules also form an ascending exhaustive chain, so a
second application of the same stabilization lemma supplies a degree for all
vectors and all functionals. The private `uniform_powerBound` packages these
two steps under finite-generation assumptions on both group-algebra modules.

The final theorem derives Noetherianity and hence finite generation from finite
length of the representation. The published
`SmoothRep.contragredient_hasFiniteLength` supplies finite length of its actual
smooth dual using precisely the displayed admissibility and compact-open
cofinality premises. Finite length of the dual supplies the other finite module
instance. Applying `uniform_powerBound` proves the exact internal target.

This is an internal algebraic proof derived from published smooth duality and
Mathlib module finiteness. It does not prove coefficientwise growth, does not
supply compact-open cofinality for a particular rational-point group, and does
not prove convergence or rational continuation of standard intertwining
integrals. Those obligations of the unchanged host theorem remain open.
