# Finite Galois discrepancies of base-change isomorphisms

Module `Langlands.GroupScheme.Rational.FiniteGaloisBaseChangeDiscrepancy`.

This supporting unit turns an actual isomorphism of base changes
`E : G_K ≅ H_K` over a finite Galois extension `K/k` into a local group
isomorphism with all-test inner discrepancy, once each Galois pullback of `E`
differs from `E` by an inner automorphism of `G_K` given by a `K`-point of the
base-changed adjoint quotient. It is a step toward the inner-discrepancy part of
the quasi-split inner-form existence theorem. Nothing here constructs a specific
Galois cocycle, a quasi-split inner form, or the host existence theorem.

## Notation

For a scheme `S`, a cover `U : Over S` and group schemes `G H` over `S`,
`LocalGroupIso.ofBaseChangeIso E` is the Library's local group isomorphism over
`U` induced by `E : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H`.
Its value at a test point `a : T ⟶ U` sends `g : T ⟶ G.X` to
`coverPointsEquiv H a ((coverPointsEquiv G a).symm g ≫ E)`, where
`coverPointsEquiv G a` is the Library's identification of points of the base
change over the test `coverTest a` with points of `G` over `T`.

`Descent.pullIso r hf hg E` is the Library's pullback of `E` along a base map
`r`, with the iterated-pullback comparisons made explicit. For a field
extension `K/k`, `ringTest k K` is the cover `Spec K → Spec k`,
`algebraBaseMap k K` its structure map and `galoisBaseMap k K σ = Spec σ` for
`σ : K ≃ₐ[k] K`.

## Statements

### General covers (namespace `LocalGroupIso`)

- `coverPointsEquiv_symm_left_fst`, `coverPointsEquiv_symm_left_snd`: the lifted
  point `(coverPointsEquiv G a).symm g` has first pullback coordinate `g.left`
  and second coordinate `a.left`.
- `ofBaseChangeIso_comp_cover`: for an endomorphism `r : U ⟶ U` of the cover,
  `(ofBaseChangeIso E).toFun (a ≫ r) g =
  (ofBaseChangeIso (Descent.pullIso r.left (Over.w r) (Over.w r) E)).toFun a g`.
  Precomposing the cover point with `r` is the same as pulling `E` back along
  `r`.
- `coverBasePoint A x` (definition): for a base point
  `x : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj A).X` of the base change of
  `A`, the point `coverPointsEquiv A (𝟙 U) x : U ⟶ A.X` of `A` over the cover.
  `coverBasePoint_left` says its underlying map is `x.left ≫ pullback.fst`.

### Adjoint quotients over a field extension (namespace `IsAdjointQuotient`)

Let `k K` be fields in universe `u` with `Algebra k K`, `G A` group schemes over
`Spec k`, `q : G ⟶ A` and `hq : IsAdjointQuotient q`. Write `hqK` for the
Library's base-changed adjoint quotient
`adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq`.

- `baseChangePointsEquiv_innerAction`: for `T : Over (Spec K)` and points `z` of
  `A_K` and `y` of `G_K` over `T`, the Library point comparison
  `baseChangePointsEquiv (algebraBaseMap k K)` turns `hqK.innerAction.act z y`
  into `hq.innerAction.act` of the compared points.
- `coverPointsEquiv_innerAction`: the same statement for `coverPointsEquiv`
  at a test point `a : T ⟶ ringTest k K`.
- `coverPointsEquiv_constantPoint`: for a base point `x` of `A_K`,
  `coverPointsEquiv A a` sends the constant family of `x` over `coverTest a`
  to `a ≫ coverBasePoint A x`.
- `ofBaseChangeIso_basePointIso_trans`: for
  `E : (baseChange (ringTest k K).hom).obj G ≅ (baseChange (ringTest k K).hom).obj H`
  and a base point `x` of `A_K`,
  `(ofBaseChangeIso (hqK.innerAction.basePointIso x ≪≫ E)).toFun a g =
  (ofBaseChangeIso E).toFun a (hq.innerAction.act (a ≫ coverBasePoint A x) g)`.
- `hasInnerDiscrepancy_of_galois_baseChange`: assume in addition
  `[FiniteDimensional k K] [IsGalois k K]`. If for every `σ : K ≃ₐ[k] K` there
  is a base point `x` of `A_K` with
  `hqK.innerAction.basePointIso x ≪≫ E =
  Descent.pullIso (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
  (galoisBaseMap_over k K σ) E`, then
  `(ofBaseChangeIso E).HasInnerDiscrepancy hq.innerAction` holds. This is the
  Library's all-test inner-discrepancy property of the local isomorphism over
  `ringTest k K` with respect to the inner action of the original adjoint
  quotient.

## Proofs

`coverPointsEquiv_symm_left_fst` rewrites `coverPointsEquiv_left` at the
inverse image. `coverPointsEquiv_symm_left_snd` is the over-condition of the
lifted point.

`ofBaseChangeIso_comp_cover` compares underlying maps through
`ofBaseChangeIso_toFun_left`. The key identity says that the lift of `g` at
`a`, followed by the inverse direct/iterated comparison and the first pullback
projection, is the lift of `g` at `a ≫ r`. It is checked on both pullback
projections, using `pullbackComparison_inv_fst`, the pullback condition and the
over-condition of the comparison. The remaining equation unfolds `pullIso` and
uses `pullbackComparison_hom_fst` and a private copy of the projection law for
base-changed homomorphisms (`baseChange_map_fst`, proved by `pullback.lift_fst`).

`baseChangePointsEquiv_innerAction` uses the Library criterion
`AutomorphicAction.hom_ext_of_local_quotient_lift` for the base-changed
quotient map, which is flat and surjective with affine source and target. After
lifting the acting point locally along `q_K`, both inner actions become
conjugations (`innerAction_act_lift` for `hqK` and for `hq`), and the point
comparison is multiplicative and natural (`baseChangePointsEquiv_naturality`,
`baseChangePointsEquiv_comp`). `coverPointsEquiv_innerAction` follows by
unfolding `coverPointsEquiv` as the point comparison followed by precomposition
with the identity-on-schemes isomorphism `coverTestIso a`, and using naturality
of the action. `coverPointsEquiv_constantPoint` compares underlying maps.

`ofBaseChangeIso_basePointIso_trans` evaluates the composite through
`AutomorphicAction.comp_basePointIso_hom`, which writes composition with
`basePointIso x` as the action of the constant family of `x`. It then
transports the action along `coverPointsEquiv` by the two preceding lemmas.

`hasInnerDiscrepancy_of_galois_baseChange` chooses the base points `x σ` and
applies `LocalGroupIso.hasInnerDiscrepancy_of_galois` (module
`Rational.FiniteGaloisOverlapDiscrepancy`) to the family
`σ ↦ coverBasePoint A (x σ)`. For each `σ` the required equation follows from
`ofBaseChangeIso_basePointIso_trans`, the hypothesis, and
`ofBaseChangeIso_comp_cover` with `r = ringTestMap k σ.toAlgHom`. The underlying
scheme map of this `r` is definitionally `galoisBaseMap k K σ`.

## Provenance

Internal. The statements make explicit the standard facts that inner
automorphisms commute with base change and that a Galois twist of a base-change
isomorphism is measured by its pullbacks along `Spec σ`. The Lean route is
internal to this Library.
