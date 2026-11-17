# Full actual semistandard spectral families

This module constructs the full index and direct sum of smooth actual coefficient
sections in Waldspurger (2003), VI.3, printed page 305. It uses the intrinsic
all-test semistandard index and the actual rational-point orbit sections of the
companion modules. The source's `Theta` consists of pairs `(O,P)`; Lean records
these as `(p,O)`, with `p` the intrinsic parabolic/Levi/radical triple. Source
coverage and uniqueness of that triple remain the explicit geometric targets in
`SemistandardSpectralIndex`, and are not assumptions of this construction.

The field `F : Type u` is any nonarchimedean local field with finite residue
field, including positive characteristic. The ambient group scheme is affine
and locally of finite type over `F`. The carrier constructions use this weaker
ambient context and the structural data of each intrinsic index, including its
connected reductive Levi. Their intended source setting is connected reductive
`G` and a maximal split torus `i`; those two hypotheses are explicit inputs
`hG` and `hi` to the standard restriction below. No splitness of the ambient
group is assumed. Representation carriers have an independent universe `uV`.

For each intrinsic index `p`, the module uses `chosenLeviModel p`, whose actual
inclusion identifies its point group with the literal subgroup `levi p` of
`G(F)`. A split component `a p` of this fixed model, its proof `ha p`, a normal
split-center image, a measurable quotient and a Haar measure `mu p` are supplied
as family parameters. They are not extra coordinates of the parabolic index.
The companion module exposes actual model-change maps and precise geometric
split-center and smoothness choice-independence targets; this module does not
prove those substantive targets.

`RationalSemistandardTheta` is the dependent sum of `p` and the actual unitary
unramified orbit in the discrete series of `levi p` modulo the split component.
`RationalSemistandardThetaSection` is the normalized product-induced coefficient
section space at the orbit's chosen actual irreducible admissible representative.
`RationalSemistandardThetaSections` is their dependent product.
`rationalSemistandardThetaComponentSpace` is the published coherent smooth
submodule; covariance under every actual inducing equivalence, including
self-twists, remains part of this submodule.

A `CompactData p` is supplied for each `p`. Its compact open subgroup, compactness,
continuous literal Levi projection and Iwasawa factorization are visible inputs.
The companion module proves closedness and algebraic point decomposition and
states the remaining projection-continuity and compact-data existence targets.

`rationalSemistandardThetaSupport` is the literal nonzero-component support in
`Theta`. `rationalSemistandardThetaSmoothSections` is its complex submodule of
componentwise coherent smooth families with finite support. This is the direct
sum prescribed in VI.3; finite support is a defining property of an input, not a
claim about Fourier families of Schwartz functions. No orbit-finiteness theorem,
Weyl invariance, projector, weighted synthesis or Plancherel assertion occurs.

The elementary laws specialize `FiniteSupportSections`: support of zero is empty,
support of a sum or scalar multiple is contained in the corresponding union or
support, component evaluation and extension by one component are complex-linear,
evaluation after extension is the identity at that component and zero elsewhere,
single-component support is contained in its singleton, and equality follows from
equality of all components. Their proofs use the generic dependent-module laws;
this algebraic packaging is internal derived content.

The canonical standard slice `RationalSemistandardStandardTheta` restricts `p`
to `standardIndex hG hi hnu I` for finite root subsets `I`, using the same chosen
model, split component and measure as the full family. The map
`rationalSemistandardStandardIndex` simply retains this pair.
`rationalSemistandardStandardIndex_finite_fibers` proves each literal fiber
finite by injection into the finite type of root subsets: after fixing `I`,
equality of image pairs determines the orbit. It uses the published
`finite_simpleRoot` theorem for connected reductive `G`, a maximal split torus
`i` and a generic cocharacter `nu`; it needs no geometric finiteness theorem
for all semistandard parabolics.

`rationalSemistandardStandardRestrict` is raw linear precomposition and
`rationalSemistandardStandardSmoothRestrict` preserves the smooth finite-support
submodule by the finite-fiber theorem. Their evaluation formulas and the exact
preimage formula for raw support are proved by definition. Comparison with the
existing `RationalStandardThetaSections` uses its own standard representing
schemes and quotient measures; the actual orbit and component comparison maps
and their substantive Prop targets are supplied separately in
`RationalSemistandardStandardComparison`.

The source map is: Waldspurger VI.3, printed p.305 (PDF p.71), `Theta` maps to
`RationalSemistandardTheta`, the component space to
`RationalSemistandardThetaComponentSpace`, and its displayed direct sum to
`rationalSemistandardThetaSmoothSections`. The support, evaluation, extension,
canonical standard slice and restriction laws are derived algebraic interfaces
for these source definitions. They assert neither coverage of every source
parabolic by the intrinsic index nor finite support of any Fourier transform.
