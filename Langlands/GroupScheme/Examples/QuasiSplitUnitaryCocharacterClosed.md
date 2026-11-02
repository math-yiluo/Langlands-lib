# Closedness of the hyperbolic unitary cocharacter

Worker 37. This module constructs the affine pullback map of the hyperbolic
cocharacter and proves the first conjunct of the published
`QuasiSplitUnitary.RankStatement`. It does not prove the upper rank bound or
construct the rank-two torus after base change.

For fields `F E : Type u` with `[Algebra F E]` and
`[Algebra.IsQuadraticExtension F E]`, a finite matrix-algebra basis `b`, and
any `c : E ≃ₐ[F] E`, the theorem `isClosedSubgroup_cocharacter b c` states that
the existing `cocharacter b c` is a closed subgroup. Nontriviality of `c` is
not needed for this part, and the argument imposes no characteristic condition.

The construction `cocharacterLaurentPoint` precomposes the cocharacter with
the published universal Laurent point `Gm.laurentPoint F`. Its source is the
actual relative spectrum of `F[t,t⁻¹]`. The definition
`cocharacterLaurentMap` pulls back relative global sections and uses
`Corepresented.affineSectionsAlgEquiv` to identify the source sections with
that Laurent algebra.

Choose the existing free-module basis `v` of `E/F`. At least one coefficient
`a = v.repr 1 k` is nonzero, since the basis representation is injective.
The existing global functions `entryCoeff` of the two diagonal matrix entries
pull back to `a t` and `a t⁻¹`. The lemmas `entryCoeff_cocharacter` and
`cocharacterLaurentMap_entryCoeff` compute these values using naturality of
the tensor coefficients and the published point formula of the cocharacter.
Multiplying each function by the scalar `a⁻¹` gives preimages of the two
Laurent generators (`cocharacterLaurentMap_T_mem`). Constants also lie in
the image because the pullback is an `F`-algebra map. Laurent-polynomial
induction, using addition and multiplication by `t` and `t⁻¹`, proves
`cocharacterLaurentMap_surjective`.

The existing unitary group scheme is affine. The affine closed-immersion
criterion applied to the surjective pullback therefore proves closedness for
`cocharacterLaurentPoint`. Finally the source isomorphism
`Gm.relativeLaurentIso` transports closedness to the original cocharacter.
The only scalar division is by the chosen nonzero coefficient `a`; in
particular the argument does not divide by two.

This construction and proof are internal and derived from the explicit
cocharacter, tensor-coordinate, and affine-scheme APIs. The mathematical
context is Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, Definitions 19.20 and 19.22, printed
pp.401–402 (PDF pp.417–418), and the split-centre unitary calculation,
Proposition 24.40, printed p.523 (PDF p.539). Those passages explain the
rank and splitting context; the implemented coordinate-surjectivity proof
is the direct argument above, not an invocation of a rank theorem.
