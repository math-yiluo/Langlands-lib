# Actual prime extraction and finite-adelic scalars

This internal unit connects the existing normalized profinite-integer/finite-adele
comparison to the canonical prime projections of the actual Tate modules. It is
derived from the imported scalar actions and the proved density of integer
residue families; it makes no new external source attribution.

`Global.finiteAdeleToPadic` evaluates an actual rational finite adele at a finite
place and applies Mathlib's rational-completion equivalence with the corresponding
p-adic field. It is a rational algebra homomorphism.

For any witness of `RationalProfiniteIntegerAdeleComparison`, the theorem
`integralEquiv_toPadic` identifies the chosen integral equivalence's local
coordinate with `ProfiniteIntegerRing.toPadic`. Both coordinate maps are
continuous. Their values agree on integer residue families by the prescribed
normalization and the integer-cast formula for the canonical p-adic projection.
Density of these families therefore makes the maps equal.

`rationalEquiv_toPadic` extends this normalization by tensor induction, using the
coupled comparison's pure-tensor formula. Its inverse form follows by applying
the forward identity to the inverse image of a finite adele.

`rationalFullToPrime_finiteAdeleAction` expresses actual prime extraction's
semilinearity for the existing finite-adelic action, with scalar map exactly
`finiteAdeleToPadic`. The proof unfolds the finite-adelic action as transport of
the rational residue action, applies the imported residue-scalar compatibility,
and uses the newly proved inverse normalization. The final theorem specializes
this result to actual abelian schemes.

No faithfulness or injectivity of one coordinate is claimed. These scalar
compatibilities do not identify a local frame coordinate space with the actual
prime-adic Tate module, and do not prove the CM small-level rigidity statement.
