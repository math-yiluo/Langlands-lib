# Murre's condition (F4′) for the two-axis class presheaf

Worker 387 wrote this module for Task 6297. It proves the published proposition
`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassArtinianLiftingStatement` by the
theorem

```
theorem noetherianTwoAxisClassArtinianLifting :
    NoetherianTwoAxisClassArtinianLiftingStatement.{u}
```

in namespace `Langlands.AlgebraicGeometry.Picard`, at arbitrary universe `u`.

## What is proved

For an abelian scheme `A` over a scheme `S`, the proof shows that the published presheaf
`TwoAxisRigidifiedLineBundle.classPresheaf A` satisfies `UnramifiedFunctor.ArtinianLifting`.
That is Murre's condition (F4′). Its value at a test object `T : Over S` is the set of
isomorphism classes of line bundles on the self-product `A_T ×_T A_T`, with compatible
trivializations along both unit axes. The statement:

- Let `Λ` be a local artinian ring with residue field `k`, and `f : Spec Λ ⟶ S`.
- Let `A'` be a `Λ`-algebra such that `Λ → A'` is injective with cokernel of length one.
- Let `ξ₀` be a class over `Spec k` and `ξ'` a class over `Spec A'` with the same image over
  `Spec (A' ⊗[Λ] k)`.
- Then `ξ₀` is the restriction of a class over `Spec Λ`.

The general theorem is `TwoAxisRigidifiedLineBundle.classPresheaf_artinianLifting A`. It holds
over every base `S`. The required theorem specializes it to `S = Spec R` with `R` noetherian;
the noetherian hypothesis is not used.

## Proof outline

Write `P_T` for the self-product `(mumfordProduct (abelian A T)).left` and `g : P_f ⟶ Spec Λ`
for the structure map of the self-product over `f`. `g` is smooth, hence flat.

1. **Ring square.** By `ArtinianColengthOne.isPullback`, `Λ` is the pullback
   `k ×_{A' ⊗[Λ] k} A'` in `CommRingCat`. The leg `A' → A' ⊗[Λ] k` is surjective with
   nilpotent kernel (`includeLeft_surjective`, `isNilpotent_ker_includeLeft`).
2. **Gluing.** Because `g` is flat, the published
   `FlatInfinitesimalGluing.affineSquareComparison_isEquivalence` says the following. Line
   bundles on the base change of `P_f` to `Spec Λ` are equivalent to gluing data: bundles on
   the base changes to `Spec k` and `Spec A'` with an isomorphism over `Spec (A' ⊗[Λ] k)`. It
   applies to the square in step 1.
3. **Comparison of base changes.** For a `Λ`-algebra `B`, the self-product over the composite
   `Spec B → Spec Λ → S` is identified with the base change of `P_f` to `Spec B`. The
   identification is natural in `B`. This turns the classes of the statement into gluing data
   for step 2.
4. **Normalization of axes.** The glued bundle may have nontrivial restrictions to the unit
   axes. The published `LineBundle.twoAxisNormalizedBundle` replaces it by a bundle with
   trivial restrictions, without changing its restriction to `Spec k`. A compatible
   rigidification then exists, and `nonempty_iso_of_carrierIso` shows that it restricts to the
   class `ξ₀`.

## Declarations

### Comparison of iterated base changes

Throughout, `T : Over S` and `U : Over T.left`.

- `selfProductComparison A T U` is the morphism
  `P_{U → T → S} ⟶ pullback U.hom (mumfordProduct (abelian A T)).hom`. It is the pullback
  lift of the structure map of the source and `productMap A (compTestHom U.hom)`. The lemmas
  `selfProductComparison_fst` and `selfProductComparison_snd` record its two components.
- `compProductInv_hom` is the second inverse law for the published pair `compProductHom` /
  `compProductInv` (module `TwoAxisValuationClassSurjectivity`). It is checked on both
  pullback projections.
- `selfProductComparison_eq` writes the comparison as
  `compProductHom A U.hom ≫ (mumfordProductBaseChangeIso _ _).hom ≫ (pullbackSymmetry _ _).hom`.
  Each component is compared with the published projection lemmas
  `selfProductBaseChangeIso_hom_snd`, `mumfordProductBaseChangeIso_hom_fst`,
  `compCarrierIso_hom_snd` and `compProductHom_baseChangeMap`. The `IsIso` instance follows,
  since each factor is an isomorphism.
- `selfProductComparison_naturality`: for `w : U ⟶ U'` in `Over T.left` and a morphism `v`
  of composite test objects with `v.left = w.left`, the comparison intertwines
  `(relativeSpace _).map w` with `productMap A v`. Both projections are checked, using
  `productMap_fst`, `carrierMap_snd`, `relativeSpace_map_snd`, `productMap_comp` and the
  triangle `Over.w w`.
- `productMap_hom`: `productMap A h` lies over `h.left`.

### Affine specialization (section `ArtinianLifting`)

Here `Λ` is a commutative ring and `f : Spec Λ ⟶ S`.

- `productStructure A f` is `g`. Its `Flat` instance comes from smoothness of the
  self-product, a pullback of the smooth `abelian A (Over.mk f)` along itself.
- `affineComparison A f B` is `selfProductComparison` at `affineBase Λ B`, for a `Λ`-algebra
  `B`. It has an `IsIso` instance and the projection lemmas `affineComparison_fst` and
  `affineComparison_snd`. The latter says the second projection is
  `productMap A (algebraOverBase f B)`.
- `affineComparison_naturality` and `inv_affineComparison_naturality`: for a `Λ`-algebra map
  `φ : B →ₐ[Λ] B'`, the comparisons intertwine
  `(relativeSpace g).map (affineBaseMap φ)` with `productMap A (algHomOver f φ)`. The second
  form uses the inverses.
- `unitBaseSection A f : P_f ⟶ (relativeSpace g).obj (affineBase Λ Λ)` is the pullback lift
  of `g` and the identity. Its condition uses `algebraMap Λ Λ = id`.
- `productMap_unitBaseSection A f B` states
  `productMap A (algebraOverBase f B) ≫ unitBaseSection A f =
  affineComparison A f B ≫ (relativeSpace g).map (affineBaseMap (Algebra.ofId Λ B))`.
  It is checked on both projections.

### The gluing step

`exists_extension` additionally assumes `[IsLocalRing Λ] [IsArtinianRing Λ]` and the two
hypotheses `hinj` and `hlen` of (F4′). It takes:

- a line bundle `D` on `P_k`, where `P_k` is the self-product over `algebraOver f k`;
- a line bundle `L` on `P_{A'}`;
- an isomorphism `φ` from the pullback of `L` along `productMap A (algHomOver f includeLeft)`
  to the pullback of `D` along `productMap A (algHomOver f includeRight)`.

It produces a line bundle `E` on `P_f` with
`(LineBundle.pullback (productMap A (algebraOverBase f k))).obj E ≅ D`.

Proof. Write `θ_B = affineComparison A f B`. Step 2 of the outline makes the published
comparison functor `PicardGroupoid.affineSquareComparison g (ofId Λ k) (ofId Λ A')
includeRight includeLeft hsq` an equivalence, hence essentially surjective. The gluing datum
consists of:

- the bundles `(inv θ_k)^* D` and `(inv θ_{A'})^* L`;
- the isomorphism `e` over the base change to `A' ⊗[Λ] k`, which is the composite of
  - `LineBundle.pullbackCompEqIso` along the equation `inv_affineComparison_naturality` for
    `includeRight`,
  - the inverse of `pullbackCompEqIso` along `inv θ_{A' ⊗ k} ≫ productMap … includeRight`,
  - the pullback of `φ.symm` along `inv θ_{A' ⊗ k}`,
  - `pullbackCompEqIso` along `inv θ_{A' ⊗ k} ≫ productMap … includeLeft`,
  - the inverse of the analogous isomorphism for `includeLeft`.

Essential surjectivity gives a line bundle `Z` on the base change of `P_f` to `Spec Λ`. Its
pullback along the base change of `Spec k → Spec Λ` is isomorphic to `(inv θ_k)^* D` (the
left component of the comparison isomorphism). Take `E = (unitBaseSection A f)^* Z`. Then
`(productMap A (algebraOverBase f k))^* E ≅ D` is the composite of:

- `pullbackCompEqIso` along `productMap_unitBaseSection`;
- the inverse of `pullbackCompEqIso` along `θ_k ≫ (relativeSpace g).map (affineBaseMap
  (ofId Λ k))`;
- the pullback along `θ_k` of the left component above;
- `pullbackCompEqIso` along `θ_k ≫ inv θ_k = 𝟙`;
- `LineBundle.pullbackId`.

### The main theorems

`classPresheaf_artinianLifting A : UnramifiedFunctor.ArtinianLifting (classPresheaf A)`.

Proof:

1. Choose representatives `D₀` of `ξ₀` and `L'` of `ξ'`.
2. The hypothesis is an equation of classes. By definition of `classesPullback`, it is the
   equation of the classes of `(relativePullback A (algHomOver f includeLeft)).obj L'` and
   `(relativePullback A (algHomOver f includeRight)).obj D₀`. `Quotient.exact` gives an
   isomorphism `φ` of rigidified bundles.
3. Forgetting the rigidifications, `exists_extension` applied to the underlying bundles of
   `D₀` and `L'` and to `φ` gives `E₀` on `P_f` and `e₀ : q^* E₀ ≅ D₀`, where
   `q = productMap A (algebraOverBase f k)`.
4. `LineBundle.twoAxisNormalizedBundle pullbackTensorComparisonIsIso` normalizes `E₀` to a
   bundle `E` with trivial axes. `LineBundle.twoAxisNormalizedBundleRigidification` gives a
   compatible rigidification `ρ` of `E`.
5. `LineBundle.twoAxisNormalizedBundleRestrictionIso` gives `q^* E ≅ D₀` on carriers. Its
   inputs are `e₀`, the axis squares `productMap_fst`, `productMap_snd`, `first_naturality`
   and `second_naturality`, and the trivializations `D₀.obj.rigidification.first.symm` and
   `.second.symm` of the axis restrictions of `D₀`.
6. The witness is the class of `ofLineBundle E ρ`. Its image under the presheaf map is the
   class of `(relativePullback A (algebraOverBase f k)).obj (ofLineBundle E ρ)`, whose
   carrier is `q^* E`. `nonempty_iso_of_carrierIso` upgrades the carrier isomorphism to an
   isomorphism of rigidified bundles, and `Quotient.sound` concludes.

`noetherianTwoAxisClassArtinianLifting` applies `classPresheaf_artinianLifting` to each
noetherian `R` and abelian scheme `A` over `Spec R`.

## Dependencies and scope

The proof uses only `propext`, `Classical.choice` and `Quot.sound`. Its import closure
contains none of the representability statements excluded by the task, and no proof of them.
The helper module `ArtinianColengthOnePullback` is new, written for this task. Every other
ingredient is published in the Library.

## Source

Condition (F4′) is Murre's, from J. P. Murre, *Representation of unramified functors.
Applications (according to unpublished results of A. Grothendieck)*, Séminaire Bourbaki exp.
294, Corollary 1, printed p. 246 (PDF p. 5), registered as
`murre-1965-bourbaki-294-unramified-functors`. The Lean form is the published
`UnramifiedFunctor.ArtinianLifting`. The proof here does not follow Murre's remark (via (F4),
(F1b) and (F5)). It glues line bundles directly along the fibre-product square
`Λ = k ×_{A' ⊗[Λ] k} A'`.

The common helper `TwoAxisRigidifiedLineBundle.compProductInv_hom` is imported from `TwoAxisValuationClassSurjectivity`.
