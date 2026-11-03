# Lang's theorem for smooth connected affine group schemes over a finite field

Author: Worker 1387.

This module transfers Lang's theorem from
[`LangCorepresented`](LangCorepresented.md) to actual group schemes, in the form
used for `Langlands.GroupScheme.FiniteFieldTorsorPointStatement`. Declarations live
in `Langlands.GroupScheme.FiniteFieldTorsorPoint`; points are the published
relative morphisms `ringTest k A ⟶ X` of
[`ProductRingPoints`](../../AlgebraicGeometry/PointTopology/ProductRingPoints.md),
with the group law of Mathlib's `Hom.group` (scoped in `CategoryTheory.MonObj`).

- `ringTestMap_eq_algSpec_map`: for a field `k` and `f : A →ₐ[k] B`,
  `ringTestMap k f = (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op`.
  Both are `Spec.map` of `f` on the underlying schemes (`ext1` and `rfl`).
- `exists_eq_inv_mul_frobenius`: let `k : Type u` be a finite field (with
  `[Fintype k]`), `H : GroupScheme (Spec (CommRingCat.of k))` with `Smooth H.X.hom`,
  `IsAffineHom H.X.hom` and `ConnectedSpace H.X.left`, and `K : Type u` an
  algebraically closed field with `[Algebra k K]`. Then for every
  `a : ringTest k K ⟶ H.X` there is `g : ringTest k K ⟶ H.X` with

  `a = g⁻¹ * (ringTestMap k (FiniteField.frobeniusAlgHom k K) ≫ g)`.

  Proof. The Library's chosen coordinate algebra `Lie.coordinateAlgebra H` with
  `Lie.coordinateIso H : (algSpec _).obj (op (Lie.coordinateAlgebra H)) ≅ H.X` is
  finitely generated over `k` (`Lie.coordinateAlgebraFiniteType`, as smooth
  morphisms are locally of finite type) and a domain
  (`CharacterLatticeProof.isDomain_coord`, which uses smoothness and
  connectedness: a smooth connected scheme over a field is integral).
  `AffineLinearEmbedding.corepresentableBy H (Lie.coordinateIso H)` corepresents
  `H.affinePointFunctor ⋙ forget GrpCat` by this algebra. The point group of
  `H.affinePointFunctor` at `CommAlgCat.of _ K` is the group of morphisms
  `(algSpec _).obj (op (CommAlgCat.of _ K)) ⟶ H.X`, which is `ringTest k K ⟶ H.X`
  with the same group law, and its functoriality is precomposition with
  `algSpec` maps. So `exists_lang_eq` gives `g` with
  `a = g⁻¹ * ((algSpec _).map (frob k _).op ≫ g)`, and
  `ringTestMap_eq_algSpec_map` rewrites this into the stated form.
