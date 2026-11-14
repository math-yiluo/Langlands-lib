# Integer normalization on finite extensions of the unramified closure

Worker 630. The theorem
`Langlands.Geometry.Building.Kottwitz.normalizedIntermediateValuation_existsUnique`
proves the published proposition
`Langlands.Geometry.Building.Kottwitz.NormalizedIntermediateValuationStatement`
in its full universe-polymorphic scope. For every nonarchimedean local field
`F` and every finite intermediate field `L` of
`SeparableClosure F / UnramifiedClosure F`, the actual spectral valuation
`intermediateValuation F L` has exactly one equivalent surjective valuation
with values in `WithZero (Multiplicative ℤ)`.

This is a derived proof using published Library results and Mathlib's
value-group normalization. Its motivating provenance is the auxiliary
normalization obligation explained in
[NormalizedValuationStatement.md](NormalizedValuationStatement.md), underlying
Kaletha–Prasad Proposition 11.1.1. The implemented proof is described below;
it does not require an additional original-source theorem.

Write \(K=\operatorname{UnramifiedClosure}(F)\), let \(v_K\) be
`MaximalUnramified.valuation F`, and set \(d=[L:K]>0\).
The published base result `MaximalUnramified.valuation_isEquiv` compares
\(v_K\) with `fixedFieldValuation F`, and
`MaximalUnramified.valuation_surjective` says that \(v_K\) is onto the
multiplicative integers with zero.

The private lemma `norm_integer_le_iff` proves
\[
v_K(N_{L/K}x)\leq v_K(N_{L/K}y)
\quad\Longleftrightarrow\quad
v_L(x)\leq v_L(y),
\]
where \(v_L\) is `intermediateValuation F L`. It applies the published identity
`SeparableInertiaNorm.val_norm_eq`, using the ambient invariance
`(ambientHyp_sepClosureValuation F).inv`: the spectral value of the norm
is \(v_L(x)^d\). Raising nonnegative real values to the positive integer
\(d\) preserves and reflects their ordering.

The private definition `normIntegerValuation` is
\(w(x)=v_K(N_{L/K}x)\). Multiplicativity and the values at zero and one
come from the field norm. The preceding order equivalence transfers the
ultrametric inequality from \(v_L\) to \(w\); this is what makes the norm
composition a valuation. The private lemma
`normIntegerValuation_isEquiv` records that equivalence.

For nontriviality, choose \(a\in K\) with \(v_K(a)=\exp(1)\).
On its image in \(L\), the norm is \(a^d\), so \(w(a)=\exp(1)^d>1\)
and is nonzero. This proves `normIntegerValuation_nontrivial`.

Mathlib supplies `w.IsRankOneDiscrete` for this nontrivial
integer-valued valuation. Its ordered value group with zero is identified
with `WithZero (Multiplicative ℤ)` by
`Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt`.
The final valuation is the restriction of \(w\) to its own value group,
followed by this ordered isomorphism. Restriction and the isomorphism are
surjective, and both preserve the valuation ordering. Thus the constructed
valuation satisfies `IsNormalizedIntermediateValuation F L`.

Finally,
`Langlands.Global.AdelicFunctoriality.valuation_eq_of_isEquiv_of_surjective`
identifies any two equivalent surjective integer valuations of a field.
Applying it through their equivalences with \(v_L\) proves uniqueness.

Only finite dimensionality over \(K\) is required of \(L\). There are no
Galois, tame, characteristic, or residue-characteristic restrictions on
this intermediate extension, and the construction uses no local-field or
completeness instance on \(K\) or \(L\).
