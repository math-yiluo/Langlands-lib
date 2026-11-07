# Descending points of algebraic spaces along products of finite free extensions

Author: Worker 105.

Helper module for the proof of Conrad's Proposition 5.2,
`Langlands.Global.AdelicSpaceLevelPointsStatement`. It contains no statement from the
literature. It is the descent step of Conrad's proof (printed p.14).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsDescent`.

Sheaf condition for one covering morphism, for an algebraic space `X` over a scheme `S` and a
morphism `f : T' ⟶ T` over `S` whose underlying morphism is flat, locally of finite
presentation and surjective:

- `isSheafFor_singleton`: `X.presheaf` is a sheaf for the presieve `{f}`. The sieve generated
  by `f` is an fppf covering sieve (the Library's `mem_fppfTopology_of_mem`), and `X` is an
  fppf sheaf.
- `pullback_injective`: pullback of sections along `f` is injective
  (`Presieve.isSeparatedFor_singleton`).
- `exists_pullback_eq`: given a pullback square `P ⇉ T'` of `f` with itself, a section over
  `T'` whose two pullbacks to `P` agree comes from a section over `T`
  (`Presieve.isSheafFor_singleton`; every pair of maps with the same composite to `T` factors
  through `P`).

Finite free extensions, for an `R`-algebra `R'` with a basis indexed by `Fin d`, `d ≥ 1`:

- `faithfullyFlat_of_basis`: `R'` is faithfully flat over `R` (Mathlib's instance for
  `Fin d →₀ R`, `d ≥ 1`).
- `spec_properties`: `Spec R' → Spec R` is flat, locally of finite presentation and surjective
  (Mathlib's `flat_and_surjective_SpecMap_iff`; finite free modules are finitely presented).

Products, for `C`-algebras `A i → B i` with compatible scalar towers:

- `changeRing_changeRing`: change of coefficients is functorial.
- `πC C A B : ∏ A i →ₐ[C] ∏ B i`, and `inlC`, `inrC : ∏ B i →ₐ[C] TensorSquares A B`, the maps
  of `ProductPointsDescent` (pure algebra module) viewed over `C`.
- `isPullback_tensorSquares b`: with uniform bases `b i`, the spectra of
  `∏ A i → ∏ B i ⇉ ∏ (B i ⊗ B i)` form a pullback square over `Spec C`. The square of rings
  is a pushout (Mathlib's `CommRingCat.isPushout_tensorProduct`, transported along the
  bijective comparison map). `Spec` turns pushouts into pullbacks
  (`isPullback_SpecMap_of_isPushout`), and `Over.forget` reflects pullbacks.
- `exists_changeRing_eq`: let `X` be a separated algebraic space over `Spec C` and `b i` uniform
  bases of rank `d ≥ 1`. A point `x' ∈ X(∏ B i)` comes from `X(∏ A i)` as soon as, for every
  `i`, its two images in `X(B i ⊗[A i] B i)` agree. The two pullbacks of `x'` to
  `X(∏ (B i ⊗ B i))` agree because their factors agree; this uses the Library's
  `separatedProductPoints_injective`, Conrad's injectivity in Proposition 5.2. Then
  `exists_pullback_eq` applies to the pullback square above.
