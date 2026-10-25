# Full Whittaker type of a rank-one quasicharacter

`Langlands.RankinSelberg.RankOneWhittakerTypeStatement` states that every
continuous complex quasicharacter of a canonical p-adic field gives a full
Whittaker-type representation of GL(1). Its action is the existing
`rankOneCharacter`: the complex scalar representation of the character composed
with the determinant. The field universe is arbitrary.

The proposition quantifies over every prime, every `PadicField`, every continuous,
nontrivial unitary additive character and every `Quasicharacter`, using the
canonical field topology. Continuity and nontriviality of the additive character
are bundled in `UnitaryAdditiveCharacter`.
It concludes all three clauses of `IsOfWhittakerType`: admissibility, finite
generation over the actual group algebra, and a linear equivalence of the entire
standard Whittaker-functional space with the complex scalars. Smoothness is part
of the admissibility conclusion, not an additional premise. No Haar measure,
conductor bound, unitarity of the multiplicative character, or irreducibility
hypothesis is imposed. The rank-one unipotent subgroup is trivial, so
`standardCharacter ψ 0` is trivial and the rank-one functional condition is
independent of the choice of `ψ` within the specified bundle.

This is an internal, derived prerequisite for using actual rank-one characters
in ramified enlargement arguments. It is not a transcription of a separately
numbered literature result. Its intended justification uses the existing
`glFunctionals_rankOne` equality, the fact that a continuous complex character
of a nonarchimedean group has open kernel, and finite-dimensional linear algebra.
The statement makes no analytic or L-factor assertion and does not depend on
factor multiplicativity.

The carrier in this statement is exactly the complex scalars. A universe-lifted
action is a later application of the published representation-equivalence
transport for full Whittaker type; it is not silently substituted here.
This module contains only the Prop-valued statement. Its proof requires a
separate checked and independently reviewed contribution.
