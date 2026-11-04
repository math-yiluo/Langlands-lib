# Coefficient decay on the actual rational uniformizer lattice

Author: Worker 19.

`rationalLatticeCoefficientDecay` proves the complete
`RationalLatticeCoefficientDecayStatement` at independent universes `u`, `v`
and `w`. It chooses a single compact-open normal basis from the supplied
simultaneous standard basis before any finite family of rays is specified.

The helper `RationalCoefficientDecay.exists_component_lift` shows that an
integral cocharacter orthogonal to a face lifts integrally through its
compatible standard split component. It factors the maximal split torus
through the represented standard Levi and applies the published equality
between the component's integral cocharacter range and the central
cocharacters of that Levi. The compatibility equation identifies the maps;
no rational or finite-index replacement of the lattice is used.

`RationalCoefficientDecay.uniformizer_mem_chambers` evaluates this lift at
the common field uniformizer. Naturality of the uniformizer section
identifies its ambient image with the original actual uniformizer power.
The formula for the restricted character norm is the residue cardinality
raised to the negative root pairing. Nonnegative pairings therefore give
membership in the weak component chamber, and positive pairings outside the
face give membership in its strict chamber.

For each ray, orthogonality on its face and positivity on every outside
simple root imply nonnegativity on all simple roots. The supplied
`StandardCocharacterStatement` gives standard witnesses for every face,
and the rays themselves are standard cocharacters for their own faces.
`rationalLatticeStrictExponent` then chooses full-center Levi points equal
to these actual uniformizer powers and proves the strict bound for every
normalized Jacquet exponent. These points are chosen before the compact
subgroup, vector and functional.

For every subgroup in the chosen basis, the simultaneous-basis Jacquet
adapter supplies the Iwahori contraction basis for each ray's parabolic.
The literal member clauses of that same basis and the chamber memberships
above give contraction at the selected central point. For the empty face,
every nonnegative integral sum of the rays is in the weak chamber. The
member clauses give a common opposite-Levi-unipotent factorization, upper
and lower conjugation inclusions, and normalization of the compact Levi
part. This supplies all three inclusions for the actual monoid homomorphism
formed by composing the additive weighted lattice sum with uniformizer
powers.

The proof applies `haarNormalizedLatticeCoefficientBound` to these actual
subgroups, central points and lattice homomorphism. The host's Jacquet
functor and the normalized functor used there agree definitionally. Its
conclusion is exactly the product bound for the original coefficient, with
positive radii whose squares times the reciprocal of each corresponding
actual radical Haar modulus are below one. The coefficient constant and
radii may depend on the compact subgroup, vector and fixed dual functional,
as in the statement. Empty finite index types are retained by the generic
coefficient theorem.

This is an internal composition of the named geometric, valuation,
compression and spectral results, rather than a separately attributed
literature theorem. It proves no simultaneous-basis existence, chamber
covering, comparison between distinct radicals' Haar moduli, double-coset
volume estimate or integrability assertion. Those remain obligations of the
complete rational strict Jacquet criterion. The argument adds no
finite-length, irreducibility or central-character premise and uses no
classification, geometric lemma, adjointness, character independence or
cuspidal-support theorem. The reused spectral proof chain retains Worker
828's credited finite fixed-vector argument in its own paired files.
