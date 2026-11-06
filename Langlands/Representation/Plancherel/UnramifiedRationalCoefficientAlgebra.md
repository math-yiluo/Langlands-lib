# Laurent coordinates on the actual universal coefficient algebra

Worker 1755.

This is an internal consequence of the published canonical rational
unramified coordinate algebra and its transport to the literal Levi point
subgroup. It supplies the scalar-ring properties needed by coefficient
compression for the existing actual universal family. It proves no
representation-theoretic finiteness assertion.

The data are a nonarchimedean local field `F : Type u`, actual group
schemes and maps `p : P ⟶ G`, `l : M ⟶ P`, and `a : A.toGrp ⟶ M`, and a
verified `ParabolicRootPresentation p l a`. The ambient group is affine
over the field and the Levi scheme is affine. Both point groups use the
canonical `rationalPointTopology`. There is no characteristic, splitness
or matrix-group restriction.

The ring is exactly `RationalNormalized.RegularAlgebra r`, namely the
existing evaluation-generated algebra for
`parabolicLeviRationalNormCharacters r`. Its indexed norm family contains
every rational character of the actual Levi. The construction does not
choose a finite subfamily or change the common kernel.

The verified rational Levi predicate in the presentation supplies
connected reductivity of `M`, hence smoothness and local finite type.
The existing `rationalCanonicalUnramifiedLaurentAlgebraEquiv` therefore
applies in the canonical point topology. Its continuity requirement has
already been proved by the canonical norm-kernel results; this module
adds no continuity premise.

`regularAlgebraLaurentEquiv` composes that equivalence with the published
`parabolicLeviRegularFunctionsEquiv r`. It identifies the additive group
algebra
`AddMonoidAlgebra ℂ (Fin (rationalImageRank M) → ℤ)` with the literal
`RegularAlgebra r` as complex algebras. The rank is the rank of the actual
rational valuation image, and rank zero is included. The monomial
evaluation theorem transports the existing canonical formula through
`parabolicLeviUnramifiedCharactersHomeomorph r`: at an actual character,
the coefficient is multiplied by the product of its canonical character
coordinates raised to the indicated integer powers.

The integer-vector group has a finite generating set. The monoid-algebra
finite-type instance and transport through the displayed equivalence
prove `regularAlgebra_finiteType`. Since the complex field is Noetherian,
the finite-type algebra theorem gives `regularAlgebra_isNoetherianRing`.
Finally the Laurent group algebra is a domain, and its multiplicative
equivalence gives `regularAlgebra_isDomain`. Domain status follows from
the Laurent comparison, rather than from embedding into all functions.
These are named theorems; no global Noetherian or domain instance is
installed.

The imported `RationalUnramifiedFunctionField` supplies the relevant
Mathlib finite-type, Noetherian and monoid-algebra results. The
mathematical provenance is entirely the current Library's proved
canonical coordinate equivalence, proved literal-Levi function-algebra
transport, and those algebraic results. No new source theorem is
asserted.

For the uniform-compression proof this discharges the scalar
Noetherianity requirement on the actual coefficient ring. Finite
generation of the induced and Jacquet compact-open fixed modules,
specialization bijectivity, eventual stability of the actual families,
and a representation-uniform exponent remain separate obligations.
