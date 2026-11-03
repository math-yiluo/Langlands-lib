# Rational points of torsors over finite fields: proof

Authors: Worker 1387 and Worker 1406.

The theorem `Langlands.GroupScheme.finiteFieldTorsorPointStatement.{u}` has type
exactly `Langlands.GroupScheme.FiniteFieldTorsorPointStatement.{u}`, imported
unchanged from [`FiniteFieldTorsorPointStatement`](FiniteFieldTorsorPointStatement.md).
For every finite field `k : Type u`, every
`H : GroupScheme (Spec (CommRingCat.of k))` with `Smooth H.X.hom`,
`IsAffineHom H.X.hom` and `ConnectedSpace H.X.left`, and every
`X : Over (Spec (CommRingCat.of k))` with an action `[ModObj H.X X]` such that
`X.hom` is flat, surjective and quasi-compact and the shear
`ModObj.leftSMul H.X X` is an isomorphism, it produces a point in
`RingPoint k X k`. The proof adds no hypothesis. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Module structure

The helper modules live in `Langlands.GroupScheme.FiniteFieldTorsorPoint`.

- [`FiniteFieldTorsorPoint/LangAlgebra`](FiniteFieldTorsorPoint/LangAlgebra.md)
  (Worker 1387): commutative algebra. Finiteness of an algebra from power
  relations among its generators, injectivity of an endomorphism of a finitely
  generated domain over which the domain is integral (by Krull dimension), and
  lifting maps to an algebraically closed field along integral extensions.
- [`FiniteFieldTorsorPoint/LangCorepresented`](FiniteFieldTorsorPoint/LangCorepresented.md)
  (Worker 1387): Lang's theorem `exists_lang_eq` for a group functor on
  `k`-algebras corepresented by a finitely generated domain. Every point `y`
  over an algebraically closed field is `x⁻¹ * F.map (frob k _) x`.
- [`FiniteFieldTorsorPoint/LangGroupScheme`](FiniteFieldTorsorPoint/LangGroupScheme.md)
  (Worker 1387): `exists_eq_inv_mul_frobenius`, Lang's theorem for a smooth
  connected affine `H` over a finite field `k`, stated for the points
  `ringTest k K ⟶ H.X` over an algebraically closed field `K` with the group law
  of Mathlib's `Hom.group`: every `a` equals
  `g⁻¹ * (ringTestMap k (FiniteField.frobeniusAlgHom k K) ≫ g)` for some `g`.
- [`FiniteFieldTorsorPoint/PointDescent`](FiniteFieldTorsorPoint/PointDescent.md)
  (Worker 1406): a Frobenius-fixed point over a field extension gives a
  `k`-point, and a nonempty scheme locally of finite type over `k` has a point
  over every algebraically closed extension.
- [`FiniteFieldTorsorPoint/TorsorAction`](FiniteFieldTorsorPoint/TorsorAction.md)
  (Worker 1406): `torsor_point_of_lang`. For `H` locally of finite type and `X`
  as in the statement, Lang's surjectivity for the points of `H` over
  `AlgebraicClosure k` (premise `hLang`) gives `Nonempty (RingPoint k X k)`.

## Final assembly

After introducing the hypotheses, the proof chooses `Fintype k` from `Finite k`
(`Fintype.ofFinite`), as the Frobenius `FiniteField.frobeniusAlgHom` needs it.
`LocallyOfFiniteType H.X.hom` is inferred from `Smooth H.X.hom` by instance, and
the connectedness hypothesis `ConnectedSpace H.X.left` is in the local context,
where instance search finds it. Then
`exists_eq_inv_mul_frobenius H (AlgebraicClosure k)` is exactly the premise
`hLang` of `torsor_point_of_lang`, and
`torsor_point_of_lang H X hfl hs hqc hiso hLang` is the conclusion.
