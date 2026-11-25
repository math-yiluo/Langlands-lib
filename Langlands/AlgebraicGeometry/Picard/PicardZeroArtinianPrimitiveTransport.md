# Artinian lifting of Picard-zero families from lifting of primitive line bundles

This module connects the lifting statement for primitive line bundles,
`Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement` (module
`Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingStatement`), to the
hypothesis `hlift` of `picardZeroArtinianLifting_of_familyLineBundle_lift` from the
module `PicardZeroArtinianLiftingReduction`. The main result is an explicitly
conditional theorem:

- `picardZeroArtinianLifting_of_primitive (hP) (hQ) :
  PicardZeroArtinianLiftingStatement`, where
  - `hP : ArtinianPrimitiveLineBundleLiftingStatement`, and
  - `hQ` says that for every local Artinian ring `B`, every abelian scheme `X` over
    `Spec B` and every line bundle `L` on `X` with `IsGeometricallyPicardZero X L`, the
    bundle `L` is primitive (`IsPrimitiveLineBundle X L`, defined below).

Neither `hP` nor `hQ` is proved or assumed anywhere else in this module. The module
proves only the glue between them and the target.

All declarations are in the namespace
`Langlands.AbelianScheme.PicardZeroArtinianLiftingReduction`.

## Provenance

The target is a derived formulation of the Artinian case of Faltings–Chai, *Degeneration
of Abelian Varieties*, Chapter I, Remark 1.5(c); see the Markdown of
`PicardZeroArtinianLiftingStatement`. `hQ` is the theorem of the square for
geometrically Picard-zero line bundles over a one-point base. `hP` is the lifting of
such primitive bundles along an elementary Artinian thickening. Both are internal
interfaces chosen to split the proof of the target into steps, and this module is
internal glue code. It does not formalize a
source theorem.

## Declarations and proofs

### Primitive line bundles

- `IsPrimitiveLineBundle X L` (a `def` valued in `Prop`), for an abelian scheme `X` over
  `T` and a line bundle `L` on `X.X.left`: there is an isomorphism
  `m^*L ≅ p₁^*L ⊗ p₂^*L` on the product `X.X ⨯ X.X` in `Over T`, where `p₁ = prod.fst`,
  `p₂ = prod.snd` and `m = p₁ * p₂` is the group law. The `let`-bindings and the
  conclusion are those of the hypothesis on `L` in
  `ArtinianPrimitiveLineBundleLiftingStatement`, with `A₀` replaced by `X`.
- `nonempty_tensor_iso_of_comp_eq`: let `F : P ⟶ Q` and `g : Y ⟶ Z` be scheme
  morphisms, and let `m, p, q : Q ⟶ Z` and `m', p', q' : P ⟶ Y` satisfy
  `r' ≫ g = F ≫ r` for each of the three pairs. Then an isomorphism
  `m^*M ≅ p^*M ⊗ q^*M` gives an isomorphism
  `m'^*(g^*M) ≅ p'^*(g^*M) ⊗ q'^*(g^*M)`. Proof: for each pair, the composite of
  `pullbackComp F r`, `pullbackCongr` and `(pullbackComp r' g)⁻¹` identifies
  `F^*(r^*M)` with `r'^*(g^*M)`. Apply `F^*` to the given isomorphism, then the tensor
  comparison `pullbackTensorComparison F`, which is an isomorphism by
  `pullbackTensorComparisonIsIso`. Finish with `tensorMap` of the two identifications.
  Its inverse is `tensorMap` of the inverses, checked with `tensorMap_comp` and
  functoriality of `tensorFunctor`.
- `isPrimitiveLineBundle_pullback`: if `f : X ⟶ Y` is a homomorphism of abelian schemes
  over `T` and `L` is primitive on `Y`, then `(LineBundle.pullback (hom f)).obj L` is
  primitive on `X`. Proof: apply the previous lemma with `g` the underlying map of `f`
  and `F = prod.map g g`. The projection squares hold by `simp`. The multiplication
  square follows from `MonObj.mul_comp` (`f` is a monoid homomorphism) and
  `MonObj.comp_mul`.

### Base-change comparison

- `totalSpaceMap_eq`: write `j = Spec φ`. The hom part of
  `baseChangeCompIso β j A : (baseChange (j ≫ β)).obj A ≅ (baseChange j).obj
  ((baseChange β).obj A)`, followed by the first projection
  `(A ×_S Spec B') ×_{Spec B'} Spec B ⟶ A ×_S Spec B'`, equals `totalSpaceMap A φ β`.
  Proof: check both projections with `pullback.hom_ext`. For the first projection,
  `GroupScheme.baseChangeCompIso_inv_fst` describes the inverse comparison, and
  `hom ≫ inv = 𝟙` rewrites the composite to `pullback.fst`. For the second projection,
  the comparison is a morphism over `Spec B` (`Over.w`), and `pullback.condition`
  reduces the claim to that fact. In both cases the remaining side is closed by
  `pullback.lift_fst` and `pullback.lift_snd`, since `totalSpaceMap` is a
  `pullback.map`.

### The transport

- `familyLineBundle_lift_of_primitive (hP) (hQ)`: proves the hypothesis `hlift` of
  `picardZeroArtinianLifting_of_familyLineBundle_lift`. Given the target data and a
  Picard-zero family `M` over `Spec B`, let `L = familyLineBundle A M` on
  `A ×_S Spec B`, and write `e = baseChangeCompIso β j A`.
  1. `hM` is `IsGeometricallyPicardZero ((baseChange (j ≫ β)).obj A) L` by definition of
     `IsPicardZeroFamily`, so `hQ` makes `L` primitive.
  2. `isPrimitiveLineBundle_pullback e.inv` makes the pullback of `L` to
     `(baseChange j).obj ((baseChange β).obj A)` primitive.
  3. `hP`, applied to the abelian scheme `(baseChange β).obj A` over `Spec B'`, gives
     `L'` on `A ×_S Spec B'` and an isomorphism from its pullback along the first
     projection to that primitive bundle.
  4. Pull this isomorphism back along `hom e.hom`. `totalSpaceMap_eq` and
     `LineBundle.pullbackCompEqIso` identify the left side with the pullback of `L'`
     along `totalSpaceMap A φ β`. On the right side, `e.hom ≫ e.inv = 𝟙`,
     `LineBundle.pullbackCompEqIso` and `LineBundle.pullbackId` give back `L`.
- `picardZeroArtinianLifting_of_primitive (hP) (hQ)`: apply
  `picardZeroArtinianLifting_of_familyLineBundle_lift` to
  `familyLineBundle_lift_of_primitive hP hQ`.
