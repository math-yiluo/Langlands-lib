# Global coefficient growth from supplied finite independent charts

`Langlands.Plancherel.RationalFiniteChartModerateGrowthStatement` is an
internal implication for an arbitrary connected reductive group over a
nonarchimedean local field. It retains a supplied maximal split torus,
cocharacter and simultaneous standard compact-open basis at a subgroup `K0`.
It also retains a finite family of charts in the actual cocharacter lattice.
Every chart has a finite integrally independent family of generators pairing
nonnegatively with every simple root. Two supplied compact subsets and a
finite set of translates cover the entire rational-point group by products
`k₁ * uniformizerPowers i (sum a, m a • gen ε a) * t * k₂`, with natural
coordinates.

The conclusion is the coefficientwise polynomial bound in the actual
residue-normalized matrix norm of any supplied closed matrix embedding.
It holds for every admissible smooth complex representation, vector and
smooth functional. The natural exponent and positive constant may depend
on this coefficient pair. The field, representation carrier, chart index
and coordinate index universes are independent.

The internal derivation combines unrestricted coefficient bounds along
weakly positive cocharacter lattices with a character positive on each
independent chart. Algebraic regular-function bounds in the closed matrix
embedding control the total natural coordinate height. The compact
polynomial-bound bridge then gives one exponent and positive constant per
chart. Finite sums dominate the chart exponents and constants, since the
actual matrix norm is at least one, giving the global estimate.

Empty coordinate families and zero-dimensional fixed-vector spaces are
included. The statement constructs no simultaneous standard basis or
global cover and does not discharge those retained structural obligations
in the full coefficientwise moderate-growth theorem. No finite-length,
splitness or characteristic restriction is added.
