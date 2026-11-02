# Actual finite-algebra universal unit and its canonical map

This module completes the internal construction of the finite-algebra unit
presheaf and its determinant-open candidate. Fix any field `k : Type u`,
any commutative `k`-algebra `A : Type u`, and a finite basis
`b : Basis (Fin n) k A`. A basis supplies the finite-dimensional
hypothesis. The construction works for every such basis and every `n`,
including zero. It does not assume that `A` is nontrivial, reduced or
separable.

The imported `presheaf k A` is an actual
`AlgebraicSpace.Presheaf (Spec k)`. Its value on an arbitrary scheme
`T : Over (Spec k)` is
`ULift (Γ(T.left ×_(Spec k) Spec A, ⊤)ˣ)`.
The equation `presheaf_obj` gives this evaluation, and
`presheaf_restriction` gives the map induced by ordinary pullback of
global functions along the actual morphism of fibre products.
`groupPresheaf k A` retains the commutative-group-valued version.
The identity and composition laws are proved in the imported
`RelativeGlobalUnits` module. All test schemes are allowed, including
empty, nonreduced and non-quasi-compact schemes.

Write `R = MvPolynomial (Fin n) k`, `g = ∑ i, X i ⊗ b i`,
`d = determinant b = det(lmul g)` and `C = Localization.Away d`.
The imported `candidate b` is the actual scheme `Spec C` over `Spec k`.
The module `FiniteAlgebraDeterminant` proves that the image of `g` in
`C ⊗[k] A` is a unit. It also proves `d = 1` for rank zero. That proof
uses the finite-free norm as the determinant of multiplication and the
empty-matrix determinant convention.

`candidateFibre b` is the actual chosen categorical fibre product
`Spec C ×_(Spec k) Spec A`.
`fibreSpecIso b` is Mathlib's canonical `pullbackSpecIso k C A`,
identifying it with `Spec (C ⊗[k] A)`. The first tensor factor is
always the candidate's coordinate ring. The two projection equations
`fibreSpecIso_hom_fst` and `fibreSpecIso_hom_snd` identify the projections
with the ordinary tensor inclusions. Thus this comparison is fixed by
the actual affine fibre-product construction, not a hypothetical
representation of the unit functor.

`fibreCoordinates b` is the induced isomorphism
`Γ(candidateFibre b, ⊤) ≅ C ⊗[k] A`, followed by the standard
global-sections isomorphism of a spectrum.
`universalUnit b` transports `algebraicUniversalUnit b` along its
inverse. It is therefore a unit of actual global functions on
`candidateFibre b`.
`universalUnit_coordinates` identifies its underlying value with the
localized generic element. Explicitly, `universalUnit_formula` says
that its image under `fibreCoordinates b` is
`∑ i, algebraMap R C (X i) ⊗ b i`.
The invertibility needed to define this unit is the proved lemma
`localizedGenericElement_isUnit`, with no nontriviality hypothesis.

`candidateMap b` is a natural transformation from the actual lifted
scheme Yoneda presheaf of `candidate b` to `presheaf k A`.
For every test scheme `T` and point `h : T ⟶ candidate b`,
`candidateMap_app` says that its value is the pullback of the same
`universalUnit b` along
`(Picard.relativeSpace (algebraSchemeMap k A)).map h`.
`candidateMap_app_val` gives the formula on underlying global functions.
`candidateMap_naturality` states that restriction along `T ⟶ U`
agrees with evaluating at the composite `T ⟶ U ⟶ candidate b`.
Its proof is the ordinary identity for composition of pullbacks.

The provenance is a direct construction from scheme fibre products,
global sections, the supplied finite basis and away-localization.
No representation theorem or chosen equivalence of functors is input.
This module constructs the canonical map; it does not assert that it
is an isomorphism or that the candidate is smooth.
