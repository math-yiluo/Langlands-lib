# The Euler characteristic of `m^* L ⊗ p^* M` on the self-product of an abelian scheme

This module proves the product-side computation in Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary version), proof of (9.11), formulas (11)–(12), printed
p.132 (PDF p.136). On an abelian scheme `A` over a field `K`, for line bundles `L` and `M`
on `A` with finite cohomology,

`χ(A ×_K A, m^* L ⊗ p₂^* M) = χ(A, L) · χ(A, M)` and
`χ(A ×_K A, m^* L ⊗ p₁^* M) = χ(A, L) · χ(A, M)`,

where the self-product is the published `mumfordProduct A` (the fibre product
`pullback A.X.hom A.X.hom`, viewed over the base through its first projection), `m` is the
published `mumfordAddition A`, `p₁` is `pullback.fst A.X.hom A.X.hom` and `p₂` is
`pullback.snd A.X.hom A.X.hom`.
EVM states the formula as `χ(m^* L ⊗ p₁^* L^{-1}) = χ(L) χ(L^{-1})`, using the isomorphism
`m × p₁`. The `p₁` form here is that statement for arbitrary `L` and `M`. It uses the shear
`(x, y) ↦ (x + y, x)`, which is EVM's `m × p₁`. The `p₂` form uses the shear
`(x, y) ↦ (x + y, y)`. Its left side is the left side of the published
`AlgClosedFieldMumfordDualEulerStatement`. Both forms hold over any field `K` for any two
line bundles; algebraic closedness, ampleness and inverses are not needed.

## Declarations

### The shear (section `Shear`, any base scheme `S`)

- `mumfordProductLift A a b`: the morphism `T ⟶ mumfordProduct A` in `Over S` with
  coordinates `a, b : T ⟶ A.X`, built from `pullback.lift`. The lemmas
  `mumfordProductLift_first` and `mumfordProductLift_second` compute its composites with
  `mumfordFirst A` and `mumfordSecond A`, and `mumfordProduct_hom_ext` says a morphism into
  the self-product is determined by these two composites.
- `mumfordShear A := mumfordProductLift A (mumfordFirst A * mumfordSecond A) (mumfordSecond A)`
  is `(x, y) ↦ (x + y, y)`, where `*` is the group structure on morphisms into the group
  object `A.X` (`open scoped CategoryTheory.MonObj`).
  `mumfordShearInv A` is `(x, y) ↦ (x - y, y)`.
- `mumfordShearIso A : mumfordProduct A ≅ mumfordProduct A` has these as its two maps. Both
  composites are checked coordinatewise with `mumfordProduct_hom_ext`, using
  `MonObj.comp_mul`, `GrpObj.comp_inv` and the group laws `mul_inv_cancel_right` and
  `inv_mul_cancel_right` in the group of morphisms into `A.X`.
- `mumfordShear_left_fst` and `mumfordShear_left_snd`: on underlying schemes, the first
  coordinate of the shear is `mumfordAddition A` (by definition
  `(mumfordFirst A * mumfordSecond A).left`) and the second is `pullback.snd`.
- `mumfordShearFst A := mumfordProductLift A (mumfordFirst A * mumfordSecond A)
  (mumfordFirst A)` is `(x, y) ↦ (x + y, x)`. `mumfordShearFstInv A :=
  mumfordProductLift A (mumfordSecond A) ((mumfordSecond A)⁻¹ * mumfordFirst A)` is
  `(u, v) ↦ (v, -v + u)`. This order of the factors does not use commutativity of the group
  law.
  `mumfordShearFstIso A` has these as its two maps, checked as for `mumfordShearIso` with
  the group laws `inv_mul_cancel_left` and `mul_inv_cancel_left`.
  `mumfordShearFst_left_fst` and `mumfordShearFst_left_snd` say that its coordinates on
  underlying schemes are `mumfordAddition A` and `pullback.fst`.
- `mumfordProductIsoOf A σ : (mumfordProduct A).left ≅ (A.X ⨯ A.X).left`, for an
  automorphism `σ` of `mumfordProduct A` in `Over S`: `σ` on underlying schemes followed by
  the inverse of Mathlib's `Over.prodLeftIsoPullback`, which compares the chosen binary
  product in `Over S` with the fibre product. The lemmas `mumfordProductIsoOf_hom_fst` and
  `mumfordProductIsoOf_hom_snd` say its composites with the two product projections are
  `σ.hom.left ≫ pullback.fst` and `σ.hom.left ≫ pullback.snd`, using
  `Over.prodLeftIsoPullback_inv_fst` and `_inv_snd`.
  `mumfordProductIsoOf_hom_comp` says it commutes with the structure maps to `S`. It
  follows from `_hom_fst` and `Over.w σ.hom`, since both structure maps factor through
  `A.X.hom`.
- `mumfordProductIsoOfPullbackIso A σ hf hg L M`: if `σ` has coordinates `f` and `g`
  (hypotheses `hf : σ.hom.left ≫ pullback.fst = f` and `hg : σ.hom.left ≫ pullback.snd = g`),
  pulling the external tensor product `pr₁^* L ⊗ pr₂^* M` on `(A.X ⨯ A.X).left` back along
  `mumfordProductIsoOf A σ` gives `f^* L ⊗ g^* M`. It is the published monoidality
  isomorphism `Langlands.Scheme.Modules.pullbackTensorIso`
  (`Modules/PullbackMonoidal.lean`, pullback commutes with tensor product), followed by
  `pullbackComp` and `pullbackCongr` with the two coordinate lemmas, applied to each tensor
  factor through `tensorFunctor`.

### The Euler characteristic (section `Euler`, any field `K`)

- `nonempty_mumfordProduct_kunnethIso_of A σ hf hg L M n`: for an automorphism `σ` of
  the self-product with coordinates `f` and `g`, line bundles `L`, `M` on `A.X.left` and
  every degree `n`, there is an isomorphism
  `H^n(mumfordProduct A, f^* L ⊗ g^* M) ≅ ⊕_{a+b=n} H^a(A, L) ⊗_K H^b(A, M)`, the target
  written as `kunnethSum` from the helper module
  `Langlands/AlgebraicGeometry/Modules/KunnethEulerProduct.lean`. It is the composite of
  three isomorphisms:
  1. `relativeCohomology` applied to `mumfordProductIsoOfPullbackIso`, which identifies the
     module with the pullback of `pr₁^* L ⊗ pr₂^* M` along `mumfordProductIsoOf A σ`;
  2. the published `relativeCohomologyPullbackIso` (`Modules/SchemeIsoCohomology.lean`:
     cohomology over `e.hom ≫ g` of a pullback along a scheme isomorphism `e` is the
     cohomology over `g`), rewritten with `mumfordProductIsoOf_hom_comp`. It identifies
     the cohomology over `(mumfordProduct A).hom` with cohomology on the categorical product
     `A.X ⨯ A.X` over `Spec K`;
  3. the published Künneth theorem `coherentFieldExternalTensorKunneth`
     (`Modules/CoherentFieldExternalTensorKunnethProof.lean`). It needs `A.X` smooth and
     proper over `Spec K`, which holds for an abelian scheme, and gives
     `H^n(pr₁^* L ⊗ pr₂^* M) ≅ ⊕_{a+b=n} H^a(L) ⊗_K H^b(M)`.
  The statement is `Nonempty` because the Künneth theorem only asserts existence.
- `nonempty_mumfordProduct_kunnethIso A L M n` and
  `nonempty_mumfordProduct_kunnethIso_fst A L M n`: the cases `σ = mumfordShearIso A`
  (`f = m`, `g = p₂`) and `σ = mumfordShearFstIso A` (`f = m`, `g = p₁`).
- `hasFiniteCohomology_mumfordAddition_tensor_snd A L M hL hM` and
  `hasFiniteCohomology_mumfordAddition_tensor_fst A L M hL hM`: if `L` and `M` have finite
  cohomology, so do `m^* L ⊗ p₂^* M` and `m^* L ⊗ p₁^* M` over `(mumfordProduct A).hom`.
  This is `hasFiniteCohomology_of_kunnethIso` from the helper module, applied to the chosen
  isomorphisms of the two previous lemmas.
- `eulerCharacteristic_mumfordAddition_tensor_snd A L M hL hM hQ` and
  `eulerCharacteristic_mumfordAddition_tensor_fst A L M hL hM hQ` (main theorems): for any
  finite-cohomology proof `hQ` of `m^* L ⊗ p^* M` over `(mumfordProduct A).hom`, where `p`
  is `p₂` and `p₁` respectively,
  `eulerCharacteristic (mumfordProduct A).hom (m^* L ⊗ p^* M) hQ =
  eulerCharacteristic A.X.hom L.obj hL * eulerCharacteristic A.X.hom M.obj hM`.
  This is `eulerCharacteristic_eq_mul_of_kunnethIso` from the helper module, applied to the
  same isomorphisms. That lemma turns a degreewise Künneth isomorphism into the product
  formula for the Euler characteristics, by comparing dimensions and multiplying
  alternating dimension polynomials.

## Use

In EVM's proof of (9.11), `L` is an ample bundle `H` and `M` is an inverse of it. EVM formula
(11) is `H^n(m^* H ⊗ p₁^* H^{-1}) ≅ ⊕_{p+q=n} H^p(H) ⊗ H^q(H^{-1})`, proved with the
isomorphism `m × p₁` (the shear `mumfordShearFstIso` here) and Künneth. The `p₁` form above
gives its Euler-characteristic consequence `χ(m^* H ⊗ p₁^* H^{-1}) = χ(H) χ(H^{-1})`, the
middle equality of EVM (12). EVM formulas (8)–(10) relate the same Euler characteristic to
`deg φ_H`. They use the higher direct images along the second projection `p₂`, which are
supported on the finite group `K(H)`. For degenerate bundles EVM (p.133) uses
`χ(m^* L ⊗ p₂^* L^{-1})`, which is the `p₂` form. This module proves only the product side
and uses no unproved Library statement. The helper module `KunnethEulerProduct` was written
by Worker 998.
