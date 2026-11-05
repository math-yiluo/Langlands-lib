# Smooth connected commutative groups killed by `p` are vector groups

Author: Worker 1519 (task `c8e71bce-b184-446c-af50-7ac4df6401a3`).

This module proves the existing proposition
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`
(module `Langlands.GroupScheme.Rational.CommutativeVectorClassificationStatement`) at
arbitrary universe `u`:

`theorem RelativeRoot.smoothCommutativePTorsionVector :
  SmoothCommutativePTorsionVectorStatement.{u}`.

The statement is unchanged. For every algebraically closed field `k` of prime
characteristic `p` and every commutative group scheme `G` over `Spec k` whose structure
morphism is smooth and affine, whose underlying space is connected, and whose points on
every scheme test `T` satisfy `x ^ p = 1`, it concludes `IsVectorGroup G.toGrp`: natural
additive coordinates of some finite dimension on all scheme tests. Dimension zero (the
trivial group) is included. No unipotence hypothesis is used.

The statement corresponds to the connected algebraically closed clause of Conrad–Gabber–
Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Lemma B.1.10, printed p.565 / PDF p.591
(registered source `conrad-gabber-prasad-2015-pseudo-reductive`). The implemented proof does
not follow the source route (composition series by `𝔾ₐ` and the Witt-vector extension); it
is purely Hopf-algebraic, as described below.

## Vector groups from primitive coordinates

In namespace `Langlands.GroupScheme.HopfPrimitive`, for a commutative Hopf algebra `A` over a
commutative ring `R` and a family `y : Fin n → A` of primitive elements:

- `familyPointsHom A hy`: the natural homomorphism `g ↦ (g(yᵢ))ᵢ` from the points of the
  cogroup of `A` to the functor `B ↦ Bⁿ`. Additivity is the Library lemma
  `HopfPrimitive.mul_unop_hom_apply` for each `yᵢ`.
- `familyCogroupHom A hy`: the corresponding cogroup homomorphism, obtained by full
  faithfulness of the Yoneda embedding for group objects, exactly as the Library's one-element
  `HopfPrimitive.cogroupHom`.
- `familyHom A hy : Spec A ⟶ VectorGroup.groupScheme R n` (via `(algSpec R).mapGrp`), whose
  underlying scheme morphism is `Spec.map (aeval y)` (`familyHom_left`, by `rfl`).
- `isoVectorGroup A hy hbij`: if `aeval y : R[X₁, …, Xₙ] → A` is bijective, the morphism
  `Spec.map (aeval y)` is an isomorphism, hence so is the underlying morphism over the base
  (reflection along `Over.forget`), and `Grp.mkIso'` yields a group-scheme isomorphism
  `Spec A ≅ VectorGroup.groupScheme R n`.

## The proof of the target

Let `A = AffineCoordinates.hopfAlgebra G.toGrp` and `e = AffineCoordinates.hopfSpecIso G.toGrp :
Spec A ≅ G.toGrp`, the Library's coordinate Hopf algebra of the affine group scheme.

1. Transport along `e` (`RelativeRoot.smooth_hom_of_iso`, `connectedSpace_left_of_iso`) makes
   `Spec A` smooth and connected. Hence `A` is a smooth `k`-algebra
   (`GradedHopf.smooth_hopfSpec_iff`), so finitely generated, and a domain
   (`GradedHopf.isDomain_of_hopfSpec`).
2. Commutativity of `G` makes `A` cocommutative: points of `Spec A` commute after composing
   with the isomorphism to `G.X` and cancelling it, and the Library lemma
   `isCocomm_of_commute` applies.
3. The exponent hypothesis gives `hA : toConv φ.toLinearMap ^ p = 1` for every `k`-algebra map
   `φ : A → k`. Mathlib's `Spec.mapMulEquiv` sends `toConv φ ^ p` to the `p`-th power of the
   corresponding `k`-point of `Spec A`; composing with the isomorphism to `G.X` (a monoid
   homomorphism on points, `MonObj.pow_comp`) and using `x ^ p = 1` for the test scheme
   `Spec k` gives that this point is trivial, so `toConv φ ^ p = 1`. Then
   `AlgHom.toLinearMap_convPow` and `AlgHom.toLinearMap_convOne` pass to the linear
   convolution dual. Only `k`-points of the exponent hypothesis are used.
4. `Langlands.Algebra.PTorsionHopf.exists_primitive_polynomial_coordinates`
   (`Langlands/Algebra/PTorsionHopf/PolynomialStructure.md`) produces `s` and primitive
   `y : Fin s → A` with `aeval y` bijective.
5. `e.symm ≪≫ HopfPrimitive.isoVectorGroup A hy hbij : G.toGrp ≅ VectorGroup.groupScheme k s`,
   and the Library equivalence `isVectorGroupOfDimension_iff_nonempty_iso` gives
   `IsVectorGroupOfDimension G.toGrp s`, hence `IsVectorGroup G.toGrp`.

## Supporting modules

The algebraic input is developed in `Langlands/Algebra/PTorsionHopf/`:
`Verschiebung` (vanishing of `p`-th powers in the convolution dual from `[p] = 0` on
`k`-points, reducedness and the Nullstellensatz), `AugmentationIdeal` (conilpotence),
`PrimitiveProducts` and `PrimitiveGeneration` (generation by primitive elements),
`MinimalRelation` (minimal relations among primitive elements are additive),
`AdditivePolynomials` (degrees of additive polynomials are powers of `p`),
`EuclidReduction` (shortening primitive generating tuples), and `PolynomialStructure`
(assembly). Each has its own Markdown.

Axioms: the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
