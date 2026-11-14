# The quotient space of a Noetherian level

Module `Langlands.AlgebraicGeometry.QuasiAffineApproximation.QuotientSpace`.

This module proves Part III, `QuotientInterface`, of the route to
`QuasiAffineSourceAFNoetherianSchemeApproximationStatement` (module
`QuasiAffineApproximation.Skeleton`). The input is a Noetherian level of the
approximation: an étale equivalence relation `E₁` with `E₁.U` and `E₁.R` affine; a
cartesian morphism `(φ₁, g₁) : E₁' ⟶ E₁` with `φ₁` finite and surjective; and a flat,
locally finitely presented, surjective `q₁ : E₁'.U ⟶ M₁` with kernel pair
`(E₁'.t, E₁'.s)`, where `M₁` is a quasi-affine Noetherian scheme. From the Noetherian
case `NoetherianSchemeQuasiAffineSourceAFStatement`, the module builds a scheme `P` in
which every finite set of points lies in an affine open, an affine morphism
`ψ : M₁ ⟶ P` and a morphism `ψV : E₁.U ⟶ P` with `q₁ ≫ ψ = φ₁ ≫ ψV`.

Geometrically, `P` represents the algebraic-space quotient `Q = E₁.U / E₁.R`. Then
`M₁ ⟶ Q` is the map induced by `φ₁`; it is finite and surjective, because its base change
along the étale atlas `E₁.U ⟶ Q` is `φ₁`. This is step 3 of the argument recorded in
`QuasiAffineSourceAFNoetherianSchemeApproximationStatement.md`: after approximation (Gross,
*Tensor generators on schemes and stacks*, Proposition 3.5, step 3; source
`gross-tensor-generators-schemes-stacks-2017`), apply the Noetherian case to the
algebraic space of the Noetherian level. The declarations below are internal helpers for
that step; their formulation is derived for this route and is not taken from the source.

## Declarations

- `exists_fac_of_kernelPair`. Let `q : U' ⟶ M` be a flat, locally finitely presented,
  surjective morphism of schemes over `S` with kernel pair `(t', s')`. Then a map
  `c` from the represented presheaf of `U'` to an fppf sheaf `F` with `t' ≫ c = s' ≫ c`
  factors as `q ≫ f`.
- `eq_of_isCartesian`, `exists_lift_of_isCartesian`, `isPullback_of_isCartesian`.
  Let `(t, s)` be the kernel pair of a map `a` from the represented presheaf of `U` to a
  presheaf `F`. Let `(t', s')` be the kernel pair of `q : U' ⟶ M` as above. Suppose
  `g : R' ⟶ R` and `φ : U' ⟶ U` satisfy `g ≫ t = t' ≫ φ`, and the square
  `g ≫ s = s' ≫ φ` is a pullback. If `f` satisfies `q ≫ f = φ ≫ a`, then the square
  `q ≫ f = φ ≫ a` (on represented presheaves) is a pullback. The first lemma gives
  uniqueness of lifts: two points of `U'` with the same images in `M` and `U` agree. The
  second gives existence: points `x` of `M` and `u` of `U` with `x ≫ f = u ≫ a` lift to a
  point of `U'`.
- `quotientInterface_of_isTerminal`. The statement of `QuotientInterface` with the base
  replaced by any affine terminal scheme `S`.
- `quotientInterface : QuotientInterface.{u}`. The instance `S = Spec (ULift ℤ)`, using
  Mathlib's `specULiftZIsTerminal`.

## Proof

1. `exists_fac_of_kernelPair`. On fppf sheaves, the map induced by `q` is locally
   surjective (`isLocallySurjective_schemeYoneda_map`), hence an epimorphism. Sheaves form
   a regular-epi category, so it is an effective epimorphism. A map that agrees on the two
   pullbacks along `q` is constant on its kernel pair: test points of the kernel pair
   factor through `R'`, because `(t', s')` is the kernel pair of `q`. The factorization
   is `EffectiveEpi.desc`.
2. `eq_of_isCartesian`. Two points `w, w'` with `w ≫ q = w' ≫ q` give a point of `R'`.
   Its image under `g` is the point of `R` determined by `w ≫ φ = w' ≫ φ`. By the
   cartesian square it equals the image of the diagonal point `(w', w')`. Hence the two
   points of `R'` agree, and so `w = w'`.
3. `exists_lift_of_isCartesian`. Base change `q` along `x` to an fppf cover
   `π : P ⟶ T` with a point `w₀ : P ⟶ U'`. The points `π ≫ u` and `w₀ ≫ φ` have the same
   image under `a`, so they define a point of `R`. With `w₀` it lifts through the
   cartesian square to a point of `R'`, whose image under `t'` is a local lift `w₁`.
   Step 2 shows that `w₁` is constant on the kernel pair of `π`. Since `π.left` is a
   flat, locally finitely presented surjection, it is an effective epimorphism of schemes
   (Library fppf descent). So `w₁` descends to `T`.
4. `isPullback_of_isCartesian`. The square is checked objectwise on types
   (`Types.isPullback_iff`): injectivity is step 2 and the existence of lifts is step 3.
5. `quotientInterface_of_isTerminal`. Let `b : E₁.U ⟶ S` be the unique map. The published
   `etaleEquivalenceRelationAlgebraicSpaceQuotient` gives an algebraic space `Q` with an
   étale surjective atlas `a` whose kernel pair is `(E₁.t, E₁.s)`. Regard `E₁'`, `M₁` and
   all maps as schemes over `S`; the squares lift from schemes to `Over S` by
   `IsPullback.of_map_of_faithful`. The map `φ ≫ a` is constant on the kernel pair of `q`,
   so step 1 gives `f₁ : M ⟶ Q` with `q ≫ f₁ = φ ≫ a`. Step 4 shows that the square with
   the étale surjective atlas `a` is cartesian. Finiteness and surjectivity of `φ₁` descend
   to `f₁` by the Library's `relative_of_isEtale_isSurjective` together with fppf descent of
   finiteness (`Morphisms.FpqcFiniteDescent`) and of surjectivity (Mathlib). `Q` is
   quasi-compact, since its atlas has affine source, and quasi-separated by
   `FinitePresentationRelationQuotient.isQuasiSeparated_of_atlas`. The required
   quasi-compactness of `prod.lift t s` is proved as in the Library's
   `FinitePresentationRelationQuotient.quotient`, from the affine `E₁.R` and the separated
   `E₁.U ⟶ S`. `NoetherianSchemeQuasiAffineSourceAFStatement` applied to `f₁` gives `P`,
   with every finite set of points in an affine open, and an isomorphism `e` from the
   presheaf of `P` to that of `Q`. Then `ψ` and `ψV` are the preimages under Yoneda of
   `f₁ ≫ e⁻¹` and `a ≫ e⁻¹`. `ψ` is finite (`isFinite_left_of_isFinite_map`), hence
   affine. The identity `q₁ ≫ ψ = φ₁ ≫ ψV` follows from `q ≫ f₁ = φ ≫ a` by faithfulness
   of Yoneda.

The common helper `exists_fac_of_kernelPair` is imported from [FppfKernelPairDescent](../FppfKernelPairDescent.md), with unchanged namespace and statement.
