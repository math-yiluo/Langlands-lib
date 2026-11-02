# The splitting of the quasi-split unitary group `U(1,1)` over `E`

Author: Worker 293. This is definition unit 3 of task
`be70310c-1939-4a82-8293-c4d33f5883ae`. It builds on unit 1,
`Langlands.GroupScheme.Examples.QuasiSplitUnitary` (Worker 399). That unit
defines the involution `σ X = J (X.map c)ᵀ J` of `Matrix (Fin 2) (Fin 2) E`,
the group scheme `groupScheme b c` over `Spec F`, the point subgroups
`matrixPoints R c` and the point equivalence `pointsEquiv`.

Throughout, `F` and `E` are fields in one universe `u`, `E` is quadratic over
`F`, and `c : E ≃ₐ[F] E` satisfies `c ≠ AlgEquiv.refl`. Every construction that
needs the nontrivial conjugation takes this as the explicit argument `hc`. No
assumption on the characteristic of `F` is made, so characteristic `2` is
covered.

## Sources and provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`:
Example 24.39 (printed p.523) defines the exchange involution
`(a, b) ↦ (b, a)` of `A × Aᵒᵖᵖ`. Proposition 24.40(b) (printed p.523) splits
an algebra with involution of the second kind with centre `K`. It uses an
extension `L` with `K ⊗ L ≅ K × K` and gives `(A ⊗ L, σ) ≅ (A₁ × A₁ᵒᵖᵖ,
exchange)`. On printed pp.524–525, `Mₙ × Mₙ` carries the involution
`σ(X, Y) = (Yᵗ, Xᵗ)`, and an element `a = (X, Y)` with `a σ(a) = 1` is shown to
be `(X, (Xᵗ)⁻¹)`. This gives the embedding `X ↦ (X, (Xᵗ)⁻¹)` of display (158),
which is the model for `pointsSplitting` below.

Here the centre is `E` and `L` is `E`, or any `E`-algebra `R`. The present
module is a derived, explicit version of this splitting. The identification
`E ⊗[F] R ≃ R × R` holds for every commutative `E`-algebra `R`, not only for
field extensions. The opposite factor is identified with `Matrix (Fin 2)
(Fin 2) R` itself through the first-kind involution `M ↦ J Mᵀ J`. The unitary
condition is the full one: there is no determinant or reduced-norm condition.
The general transport of unitary groups along an isomorphism of algebras with
involution (`AlgebraInvolution.unitaryEquiv`, `Shimura/Unitary/InvolutionBaseChangeTower`) and
the exchange involution (`AlgebraInvolution.exchange`,
`Shimura/Unitary/ExchangeInvolution`) come from the Library. So do the entrywise
product splitting `ComplexMatrix.prodAlgEquiv`, the pullback point equivalence
`GroupScheme.baseChangePointsEquiv`, `GeneralLinear.pointsEquiv` and the
point-model isomorphism `isoOfPointModels` (`GroupScheme/Torus/Split`).

## Exchange involutions and the transpose

For an algebra involution `σ` of an `R`-algebra `A`, `exchangeUnitaryEquiv σ`
is the multiplicative equivalence between the unitary group of the exchange
involution `(a, b) ↦ (σ b, σ a)` of `A × A` and `Aˣ`. It takes the first
component, and its inverse sends `a` to `(a, σ(a⁻¹))`
(`exchangeUnitaryEquiv_apply`, `exchangeUnitaryEquiv_symm_apply`).

`transposeInvolution R` is the unit-1 `matrixInvolution` with the identity
conjugation, so `M ↦ J Mᵀ J` (`transposeInvolution_apply`; entrywise
`transposeInvolution_adjoint`).

## Splitting of the coefficient algebra

`evaluation c : E →ₐ[F] E × E` is `e ↦ (e, c e)`. Its `E`-linear extension is
`tensorEvaluation c : E ⊗[F] E →ₐ[E] E × E`, with `x ⊗ y ↦ (x y, x c(y))`.
`tensorEvaluation_surjective` uses `c ≠ refl`. It picks `t` with `c t ≠ t` and
writes an explicit preimage of every pair. `tensorEvaluation_bijective` adds
that both sides have dimension two over `E`, so `tensorEquiv c hc` is an
`E`-algebra isomorphism.

For a commutative `E`-algebra `R` (with compatible `F`-algebra structure),
`algebraEquiv R c hc : R ⊗[F] E ≃ₐ[R] R × R` sends `r ⊗ e` to
`(r e, r c(e))`. It is obtained from `tensorEquiv` by cancelling base change.
`tensorSplit R c hc : E ⊗[F] R ≃ₐ[R] R × R` is the same map with the factors
in the order of unit 1 (`R` acting on the right factor). It sends `e ⊗ r` to
`(r e, r c(e))` (`tensorSplit_tmul`). Under it, `c ⊗ id` becomes the swap of
the two factors (`tensorSplit_scalarConjugation`).

## Splitting of the points

`matrixSplit R c hc` applies `tensorSplit` to every entry. It identifies
`Matrix (Fin 2) (Fin 2) (E ⊗[F] R)` with a pair of matrices over `R`
(`matrixSplit_apply`). By `matrixSplit_involution` it carries the unit-1
involution `X ↦ J (X.map c_R)ᵀ J` to the exchange involution of
`transposeInvolution R`. Composing the transported unitary groups with
`exchangeUnitaryEquiv` gives `pointsSplitting R c hc : matrixPoints R c ≃*
GL (Fin 2) R`. By `pointsSplitting_val` it is the first coordinate of
`tensorSplit`, applied entrywise. By `pointsSplitting_symm_val` the inverse
sends `h` to the matrix whose `(i, j)` entry is the preimage under `tensorSplit`
of `(hᵢⱼ, (J (h⁻¹)ᵀ J)ᵢⱼ)`. `tensorSplit_coefficientMap_fst` states that the
first coordinate commutes with every `F`-algebra map that is compatible with the
`E`-structures.

## The scheme isomorphism

`baseChangeGroupScheme b c` is the actual pullback
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj
(groupScheme b c)`, a group scheme over `Spec E`.

For every `T : Over (Spec E)`, `basePointsEquiv b c hc T` identifies its
`T`-points with `GL (Fin 2) Γ(T.left, ⊤)` in three steps. A point first
becomes a point of `groupScheme b c` over `T` regarded as an `F`-scheme
(`GroupScheme.baseChangePointsEquiv`). Then unit 1's `pointsEquiv` gives an
element of `matrixPoints`, and `pointsSplitting` applies. The coefficient ring
is the Library's `SchemeModel.restrictedSections F E T`, that is
`Γ(T.left, ⊤)` with its `F`-structure through `Spec E ⟶ Spec F`. Its
`E`-structure comes from the structure morphism of `T` (the Library instances
`sectionsSAlgebra` and `sectionsScalarTower` of `Shimura/Unitary/
SchemeScalarExtension`, used here as local instances). `basePointsEquiv_apply`
gives the entry formula. The `(i, j)` entry is the first coordinate under
`tensorSplit` of the `(i, j)` entry of the unit-1 matrix of the point.
`basePointsEquiv_naturality` states that restriction along any `a : T' ⟶ T`
applies `a.left.appTop` entrywise. Its proof combines the naturality of the
pullback point equivalence, unit 1's `pointsEquiv_naturality` and
`tensorSplit_coefficientMap_fst`.

`splittingIso b c hc` is the isomorphism of group schemes over `Spec E`

`baseChangeGroupScheme b c ≅ GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E)`

built by `isoOfPointModels` from `basePointsEquiv` and `GeneralLinear.pointsEquiv`.
`splittingIso_hom_points` and `splittingIso_inv_points` state that on `T`-points
the isomorphism and its inverse are `basePointsEquiv` and its inverse. Thus on
points over an `E`-algebra the isomorphism is induced by `e ⊗ r ↦ (e r, c(e) r)`
followed by the first projection. Test schemes are arbitrary: no affineness,
reducedness or finiteness hypothesis is imposed.

## Not included here

The task's supporting lemma that `splittingIso` carries the base change of the
cocharacter `t ↦ diag(t, t⁻¹)` of unit 2 to the diagonal cocharacter of `GL₂`
needs unit 2 (`QuasiSplitUnitaryDynamic`, Worker 399). It is not in this
module. The dynamic subgroups, rank, noncommutativity and reductivity are not
asserted here either.
