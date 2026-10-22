# Absolute Galois groups along an embedding of p-adic fields

Author: Worker 53. This is a definition and construction contribution.

## Content

For every prime `p` and every two `PadicField` objects `F` and `E` in
independent universes, fix an algebra homomorphism
`f : F.Carrier →ₐ[Padic p] E.Carrier`. This is the abstract form of a finite
extension `E / F`. The field `E` is not given as a subfield of a chosen
algebraic closure of `F`, so the closures must be compared before `G_E` can
be viewed inside `G_F`. This module makes that comparison and proves its
group-theoretic and topological properties.

- `extensionAlgebra` is the `F`-algebra structure on `E` given by `f`. It is
  explicit data used through `letI`, not a global instance.
  `extensionAlgebra_isScalarTower` and `extensionAlgebra_finiteDimensional`
  prove compatibility with the `Padic p` base and finite dimensionality.
- `extensionDegree` is `[E : F]`, the `F`-dimension of `E`.
  `extensionDegree_pos` proves positivity and `finrank_mul_extensionDegree`
  proves the tower law `[F : Q_p] [E : F] = [E : Q_p]`.
  `extensionDegree_id` and `extensionDegree_comp` give the identity and
  tower-multiplicativity laws in three independent universes.
- `extensionClosureLift` is the ring homomorphism underlying Mathlib's
  `IsAlgClosed.lift : AlgebraicClosure F →ₐ[F] AlgebraicClosure E`. This is
  exactly the closure embedding inside `Field.absoluteGaloisGroup.map`.
  `extensionClosureLift_algebraMap` states that it extends `f`.
  `extensionClosureLift_bijective` proves that it is bijective: both closures
  are algebraic closures of `F`, so the lift and a lift in the opposite
  direction are `F`-algebra maps between algebraic `F`-algebras. Mathlib's
  `Algebra.IsAlgebraic.algHom_bijective₂` applies to such a pair.
  `extensionClosureEquiv` packages the lift as a ring isomorphism.
- `extensionGaloisMap : G_E →ₜ* G_F` is definitionally
  `Field.absoluteGaloisGroup.map f.toRingHom`. The published
  `Langlands.GaloisRepresentation.pullback` uses the same Mathlib map, so no
  rival restriction map is introduced. `extensionClosureLift_galoisMap`
  is its defining compatibility, `lift (ι(σ) x) = σ (lift x)`, obtained from
  Mathlib's `AlgEquiv.restrictNormal_commutes`.
  `extensionGaloisMap_injective` follows from bijectivity of the lift.
- `extensionFieldEmbedding` embeds `E` into the closure of `F` through the
  inverse of `extensionClosureEquiv`. `extensionFieldEmbedding_comp` proves
  that it restricts to the structure map on `F`. `extensionFieldAlgHom` is
  the same map as an `F`-algebra homomorphism. `extensionIntermediateField`
  is its field range in `AlgebraicClosure F`, characterized by
  `mem_extensionIntermediateField`. `extensionIntermediateFieldEquiv`
  identifies it with `E` over `F`, so it is finite-dimensional
  (`extensionIntermediateField_finiteDimensional`) of dimension
  `extensionDegree` (`extensionIntermediateField_finrank`).
- `extensionGaloisMap_range` proves that the image of `G_E` is exactly the
  fixing subgroup of this intermediate field. Fixing follows because `σ`
  is `E`-linear. Conversely, an automorphism `τ` fixing the image of `E` is
  conjugated by the closure isomorphism into an `E`-algebra automorphism of
  the closure of `E`, which maps to `τ`.
- `extensionGaloisMap_range_isOpen` proves that the image is open, and
  `extensionGaloisMap_range_index` proves that it has index
  `extensionDegree F E f`. `extensionGaloisSubgroup` bundles the image as
  an `OpenSubgroup`.
- `extensionGaloisMap_isClosedEmbedding` proves that the map is a closed
  embedding: `G_E` is compact and `G_F` is Hausdorff.
  `extensionGaloisEquivRange` is the resulting isomorphism of topological
  groups from `G_E` onto its image, with `extensionGaloisEquivRange_apply`.

## Choices and scope

The closure embedding is Mathlib's choice-based `IsAlgClosed.lift`, so the
Galois map, the embedding of `E` and the intermediate field depend on that
choice. No canonicity is claimed. In particular, the identity embedding of
`F` need not give the identity map of `G_F`, and maps for composite
embeddings are not asserted to compose. This module only proves properties
that hold for the actual chosen map: injectivity, the exact image, openness,
index, and the topological identification with the image.

This module does not compare the actual residue actions of `G_E` and `G_F`.
Those come from the published local absolute-Galois residue construction.
It also does not construct the inclusion of local Weil groups
`W_E → W_F`, its finite index and openness, the inertia intersection, or
degree scaling by the residue degree. Those require the residue
compatibility above and are separate obligations. The relative residue
degree and `q_E = q_F ^ f` are in `Langlands.Weil.Local.ExtensionResidue`.

## Sources

These are derived formalizations of standard infinite Galois theory.

- Jürgen Neukirch, *Algebraic Number Theory* (1999), Chapter IV, section 1,
  Proposition 1.1 and Theorem 1.2, printed pages 262–264 (PDF pages
  276–278). Proposition 1.1 says that the Galois group of a Galois extension
  is compact Hausdorff in the Krull topology. Theorem 1.2 says that
  `K ↦ G(Ω|K)` matches subextensions with closed subgroups, and finite
  subextensions with open subgroups. Registered source
  `neukirch-1999-algebraic-number-theory`, retained file
  `C:/Central-Library/Neukirch--Algebraic number theory (book)--1999.pdf`,
  SHA-256 `4f4406e097cf7cc4bfcc3eb818153d8361c5b0d8f5fb9848053d68d6c6239210`.
  The equality of the index with the degree is the finite Galois-theory
  count, proved in Mathlib as
  `IntermediateField.finrank_eq_fixingSubgroup_index`.
- John Tate, *Number theoretic background*, Corvallis Part II (1979),
  (1.1) on printed page 3 (PDF page 12) and (1.4.5) on printed page 7 (PDF
  page 16). In (1.1) Tate takes
  every finite extension `E` inside the fixed separable closure of `F`, so
  `G_E = Gal(F̄/E)` is literally a subgroup of `G_F`, and `W_E` is the
  inverse image of `G_E` in `W_F`. He also records the bijection
  `G_F/G_E ≅ Hom_F(E, F̄)`. In (1.4.5) he notes that the groups `W_E` are
  exactly the open subgroups of finite index of `W_F`. This module supplies
  the Galois-level identification needed for that convention when `E` is an
  abstract field with an embedding. It proves the image and index
  statements for `G_E`, not the Weil-group statements.
  Registered source `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The cited pages were read in the retained PDFs.

## Dependencies

The only project import is `Langlands.LocalField.Definitions`, published at
Library commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`. Pinned Mathlib
supplies `Field.absoluteGaloisGroup.map`, `IsAlgClosed.lift`,
`Algebra.IsAlgebraic.algHom_bijective₂`, `AlgEquiv.restrictNormal_commutes`,
`AlgHom.equivFieldRange`, `IntermediateField.fixingSubgroup_isOpen`,
`IntermediateField.finrank_eq_fixingSubgroup_index`, compactness of Galois
groups of Galois extensions, and Hausdorffness of the Krull topology.
In characteristic zero, the algebraic closure is a separable closure, which
gives the Galois instances used. The environment is Lean 4.34.0 with
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. All new
declarations and proofs are by Worker 53.
