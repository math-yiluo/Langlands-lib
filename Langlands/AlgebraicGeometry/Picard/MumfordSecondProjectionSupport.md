# Finite support of the second-projection direct images of `m^* H ⊗ p₁^* N`

This module proves that, on an abelian variety `A` over an algebraically closed field `K`,
for an ample line bundle `H` and a tensor inverse `N` of `H`, every higher direct image

`R^n p₂,* (m^* H ⊗ p₁^* N)`, for `n : ℕ`,

along the second projection `p₂ : A ×_K A → A` has finite closed support. The theorem of the
square is a hypothesis. Here `m` is the published `mumfordAddition A`, and `p₁` and `p₂` are
`pullback.fst A.X.hom A.X.hom` and `pullback.snd A.X.hom A.X.hom`.

## Provenance

Edixhoven, van der Geer and Moonen, *Abelian Varieties* (preliminary version), proof of
(9.11), printed p.132 (PDF p.136), state that `R^n p₂,* Λ(L)` is supported on the finite
subscheme `K(L)`, for the Mumford bundle `Λ(L) = m^* L ⊗ p₁^* L^{-1} ⊗ p₂^* L^{-1}` of a
non-degenerate `L`. They get this from the Poincaré bundle, writing
`Λ(L) = (id × φ_L)^* P` and using flat base change. By the projection formula their
`R^n p₂,* Λ(L)` is `R^n p₂,* (m^* L ⊗ p₁^* L^{-1}) ⊗ L^{-1}`, so the statement here is the
same support statement for `m^* H ⊗ p₁^* H^{-1}`, for `H` ample.

The proof here does not use the Poincaré bundle or the dual abelian variety. It works one
fibre of `p₂` at a time: the restriction of `m^* H ⊗ p₁^* N` to `A × {x}` is
`t_x^* H ⊗ H^{-1}`. By the theorem of the square this bundle is translation invariant, and
it is trivial exactly when `t_x^* H ≅ H`. For an ample `H` only finitely many rational
points `x` have this property. Away from them all cohomology of the fibre vanishes, which
gives the finite support by the published `squareSecondProjectionSupport`. This route is
derived content: it combines the published statements below and is not copied from EVM.

## Declarations

### Translations (section `Translation`, any group scheme `G` over any base `S`)

- `translation_comp_translation G x y`: translation by `y` followed by translation by `x`
  is translation by `x * y`, where `*` is the group law on sections. The proof applies the
  published `points_translation` to the morphism `translation G y` and then unfolds
  `translation` with `MonObj.comp_mul` and associativity.

### The inclusion of a fibre (section `Inclusion`, any abelian scheme `A` over any base `S`)

- `mumfordSecondInclusionOver A x : A.X ⟶ mumfordProduct A` is the morphism `z ↦ (z, x)`
  in `Over S`, built with `mumfordProductLift` from the companion module
  `MumfordProductEulerCharacteristic` with coordinates `𝟙 A.X` and the constant map with
  value `x`.
- `mumfordSecondInclusionOver_left`: on underlying schemes this morphism is the published
  `squareSecondInclusion A.X.hom x.left x.w` (`Picard/SquareSecondFibre.lean`). Both are
  `pullback.lift`s, compared with `pullback.hom_ext`.
- `squareSecondInclusion_mumfordAddition A x`: `squareSecondInclusion` followed by
  `mumfordAddition A` is `(translation A.toGrp x).left`. On the level of `Over S` the
  composite is `𝟙 A.X * (const x)`, by `MonObj.comp_mul` and the two coordinate lemmas of
  `mumfordProductLift`. The published `translation` is `(const x) * 𝟙 A.X`, so the proof
  uses commutativity of the group law (`mul_comm`).

### Support (section `Support`, `K` a field)

Line bundles are compared through their isomorphism classes, the commutative group
`LineBundle.IsoClasses pullbackTensorComparisonIsIso X` of the published module
`Picard/LineBundleIsoClassGroup.lean`, with the published proof `pullbackTensorComparisonIsIso`
that pullback preserves tensor products of line bundles. In this group the class of a
tensor product is the product of the classes, and pullback along a morphism is the group
homomorphism `LineBundle.pullbackHom`; the module's local notations `cls` and `pb` stand for
`LineBundle.isoClass` and `LineBundle.pullbackHom` with that proof.

- `isoClass_eq_inv_of_tensor A H N evaluation`: if `evaluation : H ⊗ N ≅ 𝒪` then the class
  of `N` is the inverse of the class of `H`. It holds over any field; algebraic closedness
  is omitted.
- `isTranslationInvariant_translation_tensor A square H N evaluation x`: given the theorem
  of the square `square : FieldTheoremOfTheSquareStatement.{u}`, the line bundle
  `t_x^* H ⊗ N` is translation invariant in the sense of the published
  `IsTranslationInvariant A.toGrp`, where `t_x = (translation A.toGrp x).left`. For a
  section `y`, the theorem of the square gives
  `t_{x*y}^* H ⊗ H ≅ t_x^* H ⊗ t_y^* H`. With `t_y^* t_x^* = t_{x*y}^*`
  (`translation_comp_translation` and `pullbackHom_comp_eq`) and `cls N = (cls H)⁻¹`, the
  required equality `t_y^*(t_x^* H ⊗ N) ≅ t_x^* H ⊗ N` of classes becomes
  `cls(t_{x*y}^* H) / cls(t_y^* H) = cls(t_x^* H) / cls H`, which is the theorem of the
  square rearranged with `div_eq_div_iff_mul_eq_mul`. It holds over any field.
- `hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst A square H N hH
  evaluation n` (`K` algebraically closed, `H` ample, `evaluation : H ⊗ N ≅ 𝒪`): the
  module `R^n p₂,* (m^* H ⊗ p₁^* N)`, written
  `(DerivedSections.higherDirectImage (pullback.snd A.X.hom A.X.hom) n).obj Q` for
  `Q = tensorObj (m^* H) (p₁^* N)`, satisfies `HasFiniteClosedSupport`. The proof:
  1. `F` is the set of sections `x` with `t_x^* H ≅ H`. It is finite by the published
     `algClosedFieldAmpleTranslationStabilizerFinite`, since `H` is ample.
  2. The published `squareSecondProjectionSupport` reduces the claim to the vanishing of
     all cohomology `H^m(A, ι_x^* Q)` for `x ∉ F`, where
     `ι_x = squareSecondInclusion A.X.hom x.left x.w` is `z ↦ (z, x)`.
  3. `ι_x^* Q ≅ t_x^* H ⊗ N`, by comparing classes: `pb ι_x` is multiplicative,
     `ι_x ≫ m = t_x` (`squareSecondInclusion_mumfordAddition`) and `ι_x ≫ p₁ = 𝟙`
     (published `squareSecondInclusion_fst`, with `pullbackHom_id`).
  4. `t_x^* H ⊗ N` is translation invariant (`isTranslationInvariant_translation_tensor`)
     and is not trivial: a trivialization would give `cls(t_x^* H) · (cls H)⁻¹ = 1`, so
     `t_x^* H ≅ H` and `x ∈ F`. The published
     `algClosedFieldTranslationInvariantCohomologyVanishing` then gives `H^m(A, t_x^* H ⊗ N) = 0`
     for every `m`, which transfers to `ι_x^* Q` along the isomorphism of step 3.

The main theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. Its only unproved input is the hypothesis `square`; the statement
`FieldTheoremOfTheSquareStatement` is published but not yet proved in the Library.

## Use

This is the support statement needed for the Leray argument in EVM (9.11), formulas (8)–(10):
since `R^n p₂,* (m^* H ⊗ p₁^* H^{-1})` lives on finitely many closed points, the Euler
characteristic of `m^* H ⊗ p₁^* H^{-1}` on `A × A` can be computed from these direct
images. The companion module `MumfordProductEulerCharacteristic` computes the same Euler
characteristic as `χ(H) · χ(N)` by Künneth.
