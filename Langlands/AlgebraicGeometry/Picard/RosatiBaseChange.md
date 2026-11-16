# Actual Rosati conjugation and trace form under base change

This internal helper uses the existing actual canonical comparison of dual abelian schemes to transport the actual Rosati operation. Let `P` be the existing construction prerequisites, `b : S' ⟶ S` any scheme morphism in universe `u`, `A` an actual abelian scheme over `S`, `W` its actual dual datum, and `W'` any dual datum on the actual pullback.

`DualData.baseChangeIso P b W W'` is the published `dualAbelianBaseChangeIso` applied to these exact witnesses and the published `dualAbelianBaseChange` theorem. `DualData.baseChangeMap` pulls back the original map to the dual and then composes with this canonical comparison. Its underlying geometric map is the existing actual dual base-change map, with the actual dual target specified by `W'`.

`dual0_baseChange` specializes the published rational dualization naturality square to actual rational endomorphisms using the published `dualAbelianBaseChangeNaturality` theorem. The exact additivity witnesses at both schemes are retained.

`hasRationalInverse_baseChange` proves that the existing `HasRationalInverse` instance on the original map yields one on the transported map. The rational pullback functor preserves the original rational isomorphism, and the comparison of duals is already an integral isomorphism. `homToHom0_baseChangeMap` records the factorization of the actual rational transported map.

`involution_baseChange` proves equality between actual Rosati conjugation of the pulled-back rational endomorphism and pullback of its original actual Rosati conjugate. It retains the rational inverse instances on both maps; the preceding theorem supplies the second from the first. The proof transports the defining relation `lam composed with involution(a) = dual0(a) composed with lam`, uses the canonical dual naturality square, and cancels the actual rational transported polarization by its inverse. No algebraic involution law or polarization premise is used.

`traceForm_baseChange_of_comparison` works between algebraically closed characteristic-zero fields in `Type u`. Under the separately owned full `GeometricEndomorphismTraceComparisonStatement`, it proves preservation of the full actual Rosati trace form on every pair of pulled-back rational endomorphisms. The actual Rosati intertwining theorem, multiplicativity of `rationalBaseChangeEnd`, and the conditional fixed rational trace base-change theorem give the equality. In particular it includes diagonal transport and the identity geometric fibre without treating the identity pullback as definitionally equal to the original object.

This is an internal derivation from published actual dual, rational pullback and inverse constructions and the prime trace transport helper. It does not establish rational trace comparison or positive-dimensional Rosati positivity.
