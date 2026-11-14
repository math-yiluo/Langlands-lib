# Coefficient descent on recovered special fibres

This internal unit compares canonical coefficient transport with an actual
integral-model recovery. It uses the published coefficient base change,
commuting-square comparisons and generic rigidity, in arbitrary universe and
either characteristic.

The base and coefficient rings `R` and `A` are local domains with specified
fraction fields `K` and `L`, compatible scalar towers, and a supplied integral
model `M` over `R`. The actual model `N` over `A` has the prescribed generic group
obtained from that of `M`. The recovery `s` is an integral-model isomorphism from
`M.baseChange A L` to `N` over the identity of this generic group.

The integer endomorphism `a` fixes the map from `R`, the generic endomorphism `v`
fixes the map from `K`, and they satisfy the literal integer/generic square.
The supplied integral comparison `ψ` from the twist of `N` to `N` has the
canonical generic map `descentBaseChangeIso`. Its underlying integral
isomorphism is not assumed to satisfy a recovery square.

`baseChangeDescentIso` constructs the actual integral comparison on a pulled-back
model. Its underlying map is the canonical `descentBaseChangeIso` for the
integer coefficients, and its generic map is the same canonical comparison for
the fraction fields. The proof rewrites the published generic identification as
a square comparison and applies `squareComparison_semilinear` and naturality.

`recovery_descent_comm` identifies any comparison over that prescribed generic
map with canonical transport through any recovery over the identity generic
map. Both composites are model homomorphisms over the same generic morphism,
so their underlying homomorphisms agree by generic rigidity.

For a supplied residue coefficient morphism `e` from the spectrum of the residue
field of `A` to that of `R`, the literal residue/integer square defines
`residueRecoveryIso`. It first uses the inverse of `squareComparison` to
identify the two iterated pullbacks and then specializes `s`. A residue
endomorphism `r` fixes `e` and satisfies the literal residue/integer square with
`a`. `recovery_residue_descent_comm` proves that this actual recovery intertwines
`r` applied to the recovery with `ψ.residueTwistIso` and the canonical residue
coefficient comparison of `M.specialFibre`.

The proof of this residue law applies `squareComparison_naturality` to `s`,
pulls back `recovery_descent_comm`, and applies
`squareComparison_semilinear`. A private categorical lemma performs cancellation
and reassociation of these three squares. Keeping that argument abstract
avoids repeated expansion of the integral-model presentations.

For any actual downstairs group morphism `q : M.specialFibre ⟶ H`,
`residueDescendedMap` is the inverse residue recovery followed by the pullback
of `q` along `e`. `residueDescendedMap_naturality` proves its literal coefficient
square. It cancels the pullback of the residue recovery and uses the residue
recovery law and `descentBaseChangeIso_naturality` for `q`.
`RecoveredResidueDescentStatement` quantifies over every such `H` and `q`;
`recoveredResidueDescent` proves it.

The published inputs are
`Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent`,
`Langlands.GroupScheme.IntegralModel.TwistCoefficientComparison`, and
`Langlands.GroupScheme.Descent.SquareSemilinear`, through the first import,
and `Langlands.BruhatTits.IntegralModels.RelativeComponentCoefficientComparison`.
This is an internal consequence of their actual morphism constructions.

The models, their recovery, the coefficient squares, and the actual downstairs
map are supplied. No reductive quotient, full fixer-point description,
facet-parabolic correspondence, model existence, or building descent statement
is constructed. For a quotient projection identified with a
`residueDescendedMap`, the proved square applies by substitution; existence of
such a downstairs quotient and that identification remains separate.
