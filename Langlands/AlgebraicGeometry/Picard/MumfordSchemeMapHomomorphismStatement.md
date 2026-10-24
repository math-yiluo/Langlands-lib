# The homomorphism equations for the actual Mumford map

`Langlands.AbelianScheme.RelativeMumfordSchemeMapHomomorphismStatement`
asserts that the constructed Mumford classifying morphism preserves
the unit and multiplication over every quasi-separated base scheme.
It is a `Prop`-valued definition, not a proof of this assertion.

## Fixed equations

`MumfordSchemeMapHomomorphism` is the fixed-data predicate. It is
defined for any base scheme `S`, with no quasi-separatedness assumption.
Its inputs are:

- the canonical pullback-tensor comparison proposition `preservation`;
- geometric Picard-zero stability under parameter pullback, `stability`;
- the precise Mumford-family Picard-zero proposition `square`;
- an abelian scheme `A/S`, a line bundle `L` rigidified at its unit,
  an ordinary inverse bundle `M`, and the actual module evaluation
  `L tensor M ≅ O_A`;
- `hA : HasDualScheme A`, the actual universal-family existence
  property on all test schemes.

Put `f = mumfordSchemeMap preservation square A L M evaluation hA`.
This is the previously constructed unique morphism classifying
`mumfordBundle A preservation L M evaluation`. It is not a further
input. The predicate is the conjunction of two equations in `Over S`:

1. `η[A.X] ≫ f = c ≫ dualOrigin A hA`, where `η` is the existing
   group scheme unit and `c` is the canonical map from the monoidal
   terminal object to `Over.mk (identity S)`.
2. `μ[A.X] ≫ f = prod.lift (π1 ≫ f) (π2 ≫ f) ≫
   dualTensor stability A hA preservation`, where `μ` is the
   existing multiplication of `A`, and `π1,π2` are the projections
   of the cartesian monoidal product `A.X ⊗ A.X`.

The chosen monoidal terminal and binary product may differ from
`Over.mk (identity S)` and the categorical product used by
`dualTensor`. The explicit canonical maps reconcile these choices.
The published construction `dualCommGroupSchemeFromEvaluation`
has exactly the displayed origin as its unit and tensor classification
as its multiplication after this product comparison. Thus these are
the genuine homomorphism equations for its underlying parameter scheme.
No inverse for the Poincare family or coherence proof needed to bundle
that target group scheme is silently supplied by this predicate.

Both equations are equalities of scheme morphisms over `S`. They imply
the corresponding equations on every test scheme, including nonreduced
ones. The target is stronger than preservation of geometric points alone.

## Quantified target and scope

`RelativeMumfordSchemeMapHomomorphismStatement` universally quantifies
all the listed inputs and imposes `QuasiSeparatedSpace S` on the base.
It concludes the fixed-data predicate. It does not assume either of
its two equations, an arbitrary homomorphism structure, or a chosen
geometry proof for the dual. A proof may establish the geometry of the
representing scheme from its universal property and relative Picard
theory, or prove the equations directly using line bundles.

The explicit `square` proof is used to define the map whose equations
are asserted; Picard-zero membership is a separate target.
Representability is an explicit hypothesis. Neither representability,
Picard-zero membership, nor this homomorphism theorem is proved here.
The fixed predicate is available over arbitrary bases; this module
only states its universal validity over quasi-separated bases.

## Source and derived provenance

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision dated March 14, 2021:

- Construction 1.3.2.7, printed p.75 (PDF p.103), constructs the
  morphism classifying the three-factor Mumford bundle, states that it
  sends the unit to the dual unit, and invokes Corollary 1.3.1.6 for
  its homomorphism property.
- Corollary 1.3.1.6 and its proof, printed pp.70–71 (PDF pp.98–99),
  assert that a unit-preserving morphism from an abelian scheme to
  a separated group scheme of finite presentation is a homomorphism.
- Theorem 1.3.2.3, printed p.74 (PDF p.102), supplies the dual
  abelian scheme representing the rigidified Picard-zero functor.
  The conventions on printed p.xxvi (PDF p.26) require schemes
  to be quasi-separated.

Registered source: `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The cited construction, corollary, proof, and representability theorem
were read in the original PDF. The author's March 14, 2021 errata,
registered `lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9 in this development.

The formulation is derived because the Library uses a parameter-first
product, actual translation-invariance on geometric fibres for
Picard-zero, and a chosen parameter scheme with universal family.
Lan uses the second factor as parameter. Commutativity of addition and
symmetry of tensor explain the exchange of factors. The ordinary inverse
`M` and its evaluation identify the implemented three-factor bundle with
the source's inverse-bundle formula.

A proof must compare these actual families and their rigidifications,
identify the source's dual with the chosen representing scheme using the
full universal property, and match its origin and multiplication with
trivial-family and tensor-family classification. For a route through
Corollary 1.3.1.6, separatedness and finite presentation of that group
scheme must be established; they are not consequences of a mere
set of geometric points. The geometric Picard-zero/source comparison
must also be justified. These comparisons are proof obligations, not
conclusions of this statement module.
