# The general linear group scheme from explicit matrix coordinates

Author: Worker 223.

This module constructs, for a finite index type `n` and a commutative ring `R`,
the general linear group scheme over `Spec R`. It starts from an explicit
coordinate algebra. It proves that this algebra corepresents the functor of
invertible matrices, and it does not assume that corepresentation. It then
recovers the points over every test scheme `T` over `Spec R` as invertible
matrices over `Γ(T, 𝒪_T)`.

All declarations are in the namespace `Langlands.GroupScheme.GeneralLinear`.
The index `n : Type` is any type with `[Fintype n]` and `[DecidableEq n]`. The
case of `d × d` matrices is `n = Fin d`. `GL n S` is Mathlib's
`Matrix.GeneralLinearGroup n S`, the unit group `(Matrix n n S)ˣ`. The ring
`R`, its algebras and the point groups use one arbitrary universe `u`.

## Source

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter III, Example 9 on printed p. 33 (PDF p. 37):

> Let V be a finite dimensional vector space over a field k. Then we can form
> the group variety GL(V) over k. If T = Spec(R) is an affine k-scheme then
> GL(V)(T) is the group of invertible R-linear transformations of V ⊗_k R. If
> d = dim_k(V) then GL(V) is non-canonically (choice of a k-basis for V)
> isomorphic to the group variety GL_{d,k} of invertible d×d matrices; as a
> scheme the latter is given by GL_{d,k} = Spec(k[T_ij, U; 1 ⩽ i, j ⩽ d]/(det·U − 1)),
> where det ∈ k[T_ij] is the determinant polynomial. (So "U = det⁻¹".) We leave
> it to the reader to write out the formulas for the group law.
>
> More generally, if V is a vector bundle on a scheme S then we can form the
> group scheme GL(V/S) whose T-valued points are the vector bundle
> automorphisms of V_T over T. If V has rank d then this group scheme is
> locally on S isomorphic to a group scheme GL_{d,S} of invertible d×d
> matrices.

The registered source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
kept at
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
PDF pp. 36–37 were read.

The module formalizes the object `GL_{d,S}` "of invertible d×d matrices" for an
affine base `S = Spec R`. It uses a different presentation of the coordinate
ring from the source's displayed one. The source adjoins one variable `U` for
the inverse of the determinant. Here there are variables for the entries of a
matrix `X` and of a second matrix `Y`, modulo the entries of `X Y − 1` and
`Y X − 1`. Both rings corepresent the functor of invertible matrices; the
module proves this for its own ring only. It does not construct an isomorphism
with the determinant presentation. The group law is not written as Hopf algebra
formulas, which the source leaves to the reader. It is induced from matrix
multiplication through the proved corepresentation, by the Library's
`Langlands.GroupScheme.Corepresented` construction. The vector-bundle groups
`GL(V/S)` and local triviality are not formalized.

## The coordinate ring

`Coordinate n` is the type of polynomial variables. It has a variable
`entry i j` and a variable `inverseEntry i j` for each pair `i j : n`.
`genericMatrix n R` is the matrix over `MvPolynomial (Coordinate n) R` whose
`(i, j)` entry is `X (entry i j)`. `genericInverse n R` is the matrix whose
`(i, j)` entry is `X (inverseEntry i j)`. `relations n R` is the set of all
entries of `genericMatrix * genericInverse − 1` and of
`genericInverse * genericMatrix − 1`. `ideal n R` is the ideal they span.
`CoordinateRing n R` is the quotient of the polynomial ring by this ideal, and
`quotient n R` is the quotient map as an `R`-algebra map.

`ideal_le_ker` states that an `R`-algebra map `ψ` out of the polynomial ring
kills the ideal whenever the images of the two generic matrices under
`ψ.mapMatrix` are mutually inverse. Its proof checks each generator.
`quotient_mapMatrix_mul_inverse` and `quotient_mapMatrix_inverse_mul` prove that
the images of the two generic matrices in the coordinate ring are mutually
inverse, because every generator of the ideal maps to zero.
`universal n R : GL n (CoordinateRing n R)` is the resulting universal
invertible matrix. `universal_apply` and `universal_inv_apply` identify its
entries and the entries of its inverse with the images of the variables.

## Classification of algebra maps

Let `S` be a commutative `R`-algebra.
For `f : CoordinateRing n R →ₐ[R] S`, `point f : GL n S` applies `f` to every
entry of the universal matrix, by `Matrix.GeneralLinearGroup.map`.
`point_apply` and `point_inv_apply` give its entries and those of its inverse.
`point_comp` states that `point (g.comp f)` is `point f` with `g` applied
entrywise. `point_id` states that the identity map gives the universal matrix.

Conversely, for `g : GL n S`, `values g` sends `entry i j` to `g i j` and
`inverseEntry i j` to `g⁻¹ i j`. By `aeval_mapMatrix_genericMatrix` and
`aeval_mapMatrix_genericInverse`, evaluation at `values g` sends the generic
matrices to `g` and `g⁻¹`. As `g` is invertible, `ideal_le_ker` applies, and
`classify g : CoordinateRing n R →ₐ[R] S` is the induced map on the quotient.
`classify_comp_quotient` and `classify_quotient` state that it is evaluation at
`values g` on polynomials. `classify_entry` and `classify_inverseEntry` give its
values on the coordinates.

`homEquiv : (CoordinateRing n R →ₐ[R] S) ≃ GL n S` has forward map `point` and
inverse `classify`. One composite is the identity because algebra maps out of
the quotient are determined on the variables
(`Ideal.Quotient.algHom_ext` and `MvPolynomial.algHom_ext`). The other is the
identity because both matrices have the same entries. `classify_point` and
`point_classify` restate the two identities. `classify_map` is the naturality of
`classify`: applying `h : S →ₐ[R] T` entrywise to `g` gives `h.comp (classify g)`.
It follows from `point_comp` and injectivity of `homEquiv`.
`classify_universal` states that the universal matrix is classified by the
identity map.

## The group scheme

`functor n R : CommAlgCat R ⥤ GrpCat` sends `S` to the group `GL n S`. It sends
an algebra map `f` to `Matrix.GeneralLinearGroup.map` of `f`, which applies `f`
to every entry. The functor laws hold by definition. `functor_obj` and
`functor_map_apply` record these values. `coordinateAlgebra n R` is
`CoordinateRing n R` as an object of `CommAlgCat R`.

`corepresentableBy n R` is a proved corepresentation of the underlying
set-valued functor by `coordinateAlgebra n R`. Its equivalence is `point`, with
inverse `classify`. Its naturality field is `point_comp`.
`corepresentableBy_homEquiv` and `corepresentableBy_homEquiv_symm` record the
two maps.

`groupScheme n R : GroupScheme (Spec R)` is `Corepresented.groupScheme` applied
to `functor n R` and `corepresentableBy n R`. So it is the image of the
corresponding cogroup object under the relative spectrum functor `algSpec R`.
`groupScheme_X` identifies its underlying object over `Spec R` with
`(algSpec R).obj (op (coordinateAlgebra n R))`. `groupScheme_left` identifies
its underlying scheme with `Spec (CoordinateRing n R)`. `groupScheme_hom`
identifies its structure morphism with `Spec.map` of the algebra map
`R → CoordinateRing n R`. All three hold by definition.

The instance `isAffine_groupScheme` states that the underlying scheme is affine,
since it is a spectrum. The instance `isAffineHom_groupScheme` states that the
structure morphism is affine. Its proof is Mathlib's `isAffineHom_of_isAffine`,
because the morphism goes between the affine schemes `Spec (CoordinateRing n R)`
and `Spec R`.

`entrySection n R i j` and `inverseEntrySection n R i j` are the global
functions on the group scheme given by the coordinates `entry i j` and
`inverseEntry i j`. They are transported along the inverse of
`Scheme.ΓSpecIso`.

## Points on every test scheme

For `T : Over (Spec R)`,
`pointsEquiv n R T : (T ⟶ (groupScheme n R).X) ≃* GL n Γ(T.left, ⊤)` is
`Corepresented.pointsEquiv` for this functor and corepresentation. It is a
group isomorphism. The source group is the group of morphisms into the group
object, so the multiplicativity of `pointsEquiv` is the statement that the
group law of the scheme is matrix multiplication.

`pointsEquiv_apply` states that the matrix of `x` is `point` of the algebra map
adjoint to `x` under `algΓAlgSpecAdjunction R`.
`adjunction_homEquiv_symm_apply` identifies that adjoint map: it sends `b` to
the pullback along `x.left` of the global function corresponding to `b`. Its
proof uses Mathlib's `Adjunction.homEquiv_counit` and then unfolds definitions.
The resulting evaluation lemmas are:

- `pointsEquiv_apply_apply`: the `(i, j)` entry of the matrix of `x` is
  `x.left.appTop (entrySection n R i j)`;
- `pointsEquiv_inv_apply`: the `(i, j)` entry of its inverse is
  `x.left.appTop (inverseEntrySection n R i j)`;
- `points_ext`: two points with the same matrix entries are equal;
- `pointsEquiv_symm_apply`: the point with matrix `g` is the adjoint of the
  algebra map `classify g`. Its proof applies `pointsEquiv_apply` to that
  adjoint and uses `point_classify`.

`pointsEquiv_naturality` is `Corepresented.pointsEquiv_naturality`. For a
morphism `a : T' ⟶ T` over `Spec R`, the matrix of `a ≫ x` is the matrix of
`x` with the pullback `a.left.appTop` applied to every entry.
`pointsEquiv_comp_apply` states this entrywise.

The group operations:

- `pointsEquiv_mul`, `pointsEquiv_one` and `pointsEquiv_inv` state that the
  product, identity and inverse of points become the matrix product, identity
  matrix and matrix inverse;
- `pointsEquiv_lift_μ`: composing the pair `(x, y)` with the actual
  multiplication morphism `μ` gives the product of the matrices of `x` and `y`;
- `pointsEquiv_toUnit_η`: the unit morphism `η`, precomposed with the map to
  the terminal object, gives the identity matrix;
- `pointsEquiv_comp_ι`: composing with the inversion morphism `ι` inverts the
  matrix;
- `pointsEquiv_μ`: the matrix of `μ` itself, as a point over the product of
  the group scheme with itself, is the product of the matrices of the two
  projections.

These follow from the first three and the definitions of the group structure
on morphisms into a group object (`Hom.mul_def`, `Hom.one_def`, `Hom.inv_def`).
`pointsEquiv_id_apply` and `pointsEquiv_id_inv_apply` state that the identity
morphism of the group scheme, as a point, has the coordinate functions
`entrySection` and `inverseEntrySection` as the entries of its matrix and of
the inverse matrix.

## Affine test schemes

For a commutative `R`-algebra `S`, `affinePointsEquiv n R S` is
`Corepresented.affinePointsEquiv`. It identifies the points over
`(algSpec R).obj (op S)` with `GL n S` as groups.
`affinePointsEquiv_map` states that the spectrum of an algebra map `f` out of
the coordinate algebra corresponds to `point f`. `affinePointsEquiv_symm_apply`
states that the point with matrix `g` is the spectrum of `classify g`.
`affinePointsEquiv_naturality` states that precomposing with the spectrum of
`g : S ⟶ T` applies `g` to every entry. `pointsEquiv_eq_affinePointsEquiv`
compares the two equivalences on an affine test scheme: the global-section
matrix is the affine matrix with the inverse of the Library's
`Corepresented.affineSectionsIso S` applied entrywise.

## Scope

The module constructs only this explicit scheme and its point API. It does not
prove smoothness, finite presentation, reductivity or base-change
isomorphisms. It does not construct a comparison with the determinant
presentation or with vector-bundle groups `GL(V/S)`. The base scheme is the
affine scheme `Spec R`.
