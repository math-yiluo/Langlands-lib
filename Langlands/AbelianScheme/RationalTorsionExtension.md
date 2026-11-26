# Rational torsion after a finite extension of the base field

The main theorem `Langlands.AbelianScheme.exists_finite_hasRationalGeometricTorsion`
takes a field `K`, an abelian variety `B` over `K`, and a natural number
`n > 0` that is a unit of `K`. It produces a field `L` with a `K`-algebra
structure, finite dimensional over `K`. For the base change of `B` along
`Spec L → Spec K`, every `n`-torsion point over `AlgebraicClosure L` is
defined over `L`. This is `HasRationalGeometricTorsion` of
`Langlands/AbelianScheme/RaynaudSemiabelianCriterionStatement.lean`.

## Algebra

For a finite `K`-algebra `A`, `basisMinpolyProduct K A` is the product of
the minimal polynomials of the vectors of the basis
`Module.Free.chooseBasis K A`. It is nonzero, every element of a finite
algebra being integral. Let `L` be a field over `K` in which the image of
this polynomial splits, and let `Ω` be an extension field of `L`. Then
`exists_algHom_factor_of_splits` proves that every `K`-algebra map
`φ : A → Ω` factors through `L → Ω`. The minimal polynomial of a basis
vector `b` divides the product, so it splits in `L`. The value `φ b` is a
root in `Ω` of that polynomial, so it lies in the image of `L` by Mathlib's
`Polynomial.Splits.mem_range_of_isRoot`. The basis spans `A`, and the image
of `L` is a subalgebra, so all of `φ(A)` lies in it. The factorization is
`φ` with its codomain restricted to the image of `L`, followed by the
inverse of the isomorphism `AlgEquiv.ofInjective` from `L` onto its image.

## Points of a finite scheme over a field

Let `f : X → Spec K` be a finite morphism. Then `X` is affine, and
`Γ(X, ⊤)` is a finite `K`-algebra through `coordinateAlgebra f` (from
`Langlands/AlgebraicGeometry/FiniteEtale/GeometricCardinality.lean`).

- `pointAlgHom` turns a point `x : Spec Ω → X` with `x ≫ f` equal to
  `Spec Ω → Spec K` into the `K`-algebra map induced on global sections,
  composed with `Γ(Spec Ω, ⊤) ≅ Ω`. Its compatibility with `K` follows from
  the naturality `Scheme.ΓSpecIso_naturality`.
- `specMap_isoSpec_inv_appTop` shows that `Spec.map φ ≫ X.isoSpec.inv`
  induces `φ` on global sections.
- `exists_finite_pointFactorization` takes for `L` the splitting field of
  `basisMinpolyProduct K Γ(X, ⊤)`, which is finite over `K`. For every
  extension field `Ω` of `L` and every point `x` as above, the algebra
  result factors `pointAlgHom` through a `K`-algebra map
  `ψ : Γ(X, ⊤) → L`. Then `y = Spec.map ψ ≫ X.isoSpec.inv` lies over
  `Spec K`, and the composite of `Spec Ω → Spec L` with `y` is `x`. Both
  identities are checked on global sections with `ext_of_isAffine`, since
  `Spec K` and `X` are affine.

`specAlgebraMap_comp` identifies the composite `Spec Ω → Spec L → Spec K`
with `Spec Ω → Spec K` for a scalar tower `K → L → Ω`.

## Torsion of the base change

For a base change along `b : S' → S`, the Library's
`GroupScheme.baseChangePointsEquiv` is the pullback adjunction on points.
It is a group isomorphism. If a point `x` of the base change satisfies
`x ^ n = 1`, so does its image. `GroupScheme.existsUnique_torsion_lift_iff`
then lifts the image to the torsion subgroup scheme `torsion G n`. This is
`exists_torsion_lift_baseChange`. The lemma `baseChange_point_restrict`
treats a lift `z` of this kind, a morphism `a : T → T₀` of test schemes
over `S'`, and a point `w` of the torsion subgroup scheme over `T₀` with
`a ≫ w = z` on underlying schemes. It shows that `a` composed with the point
of the base change corresponding to `w` is `x`. The proof uses the
naturality `GroupScheme.baseChangePointsEquiv_naturality` and injectivity
of the adjunction.

## Proof of the main theorem

Since `n` is a positive unit of `K`, it is a unit of `Γ(Spec K, ⊤)`. The
Library's `torsionFiniteEtale` then makes the structure morphism of
`torsion B n` finite. Let `L` be the field of
`exists_finite_pointFactorization` for this morphism. Take an `n`-torsion
point `x` of the base change over `AlgebraicClosure L`. By
`exists_torsion_lift_baseChange` it corresponds to a point `z` of
`torsion B n` over `Spec (AlgebraicClosure L) → Spec K`. The factorization
gives `y₀ : Spec L → torsion B n` over `Spec K` whose composite with
`Spec (AlgebraicClosure L) → Spec L` is `z`. By `baseChange_point_restrict`,
the `L`-point of the base change corresponding to `y₀` restricts to `x`.

## Provenance

This is the elementary fact that the `n`-torsion points of an abelian
variety are defined over a finite extension of the base field. It is
derived here from the Library's finiteness of torsion,
`torsionFiniteEtale`; étaleness is not used. The splitting field of the
minimal polynomials of a basis of the coordinate algebra of the torsion
contains the values of all its points.
