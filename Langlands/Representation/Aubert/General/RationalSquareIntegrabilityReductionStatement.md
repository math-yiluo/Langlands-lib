# Reduction of strict Jacquet square integrability to joint geometry

`Langlands.Aubert.General.RationalPointFamily.RationalStrictJacquetSquareIntegrabilityReductionStatement.{u,v}`
is an internal implication from
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`
to the complete published
`Langlands.Aubert.General.RationalPointFamily.RationalStrictJacquetSquareIntegrabilityStatement.{u,v}`.
There are no parameters outside this implication. The field and representation
universe parameters remain independent.

The premise asks for actual apartment data and one special vertex, the associated
compact open subgroup, a represented torus centralizer with its character
comparison, compatible standard-Levi Cartan data, and a simultaneous standard
compact-open basis, all sharing that vertex and torus. This implication does not
construct that geometric witness.

The conclusion is the original rational-point criterion with every quantifier
and premise preserved. It covers connected reductive groups over arbitrary
nonarchimedean local fields, the canonical evaluation topology, the actual
normalized standard Jacquet functors and strict central exponent bounds,
admissible representations with a genuine unitary central character, and every
supplied Borel Haar measure on the quotient by the full actual group center.
It retains the nonsplit, non-quasisplit, positive-characteristic and empty-root
cases, and adds no finite-length or irreducibility premise.

This statement is derived for the proof architecture of the criterion. The
intended argument uses the common geometric witness to obtain a finite chamber
lattice cover, uniform coefficient decay on compact translates, and matching
upper quotient-cell volumes with the literal per-ray Haar weights. A finite
lattice integration theorem then gives the conclusion. The geometric existence
premise is therefore a remaining structural proof obligation; this intermediate
implication alone does not prove the unconditional criterion. Its provenance is
this internal composition of the named interfaces, not a new assertion attributed
to an external source.
