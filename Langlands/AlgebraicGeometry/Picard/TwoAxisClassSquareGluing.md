# Gluing two-axis classes along ring pullback squares

Worker 387 wrote this module for Task 6297, as support for the proof of Murre's condition
(F7) in `TwoAxisClassOneDimensionalLiftingProof`. It generalizes the gluing step of (F4′)
in `TwoAxisClassArtinianLiftingProof` (`exists_extension` and `classPresheaf_artinianLifting`).
The square there was the specific square `Λ = k ×_{A' ⊗[Λ] k} A'`. Here it is any ring
pullback square of `Λ`-algebras with one leg surjective with nilpotent kernel. The
declarations are in namespace `Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle`,
at an arbitrary universe `u`.

## Setting

- `A : Langlands.AbelianScheme S` over a scheme `S`.
- `Λ` a commutative ring and `f : Spec Λ ⟶ S`.
- `Λ`-algebras `R`, `A'`, `B'`, `C` and `Λ`-algebra maps `p : R → A'`, `q : R → B'`,
  `a : A' → C`, `b : B' → C`.
- `hsq`: the square of `CommRingCat.ofHom`s of `p`, `q`, `a`, `b` is an `IsPullback`, so
  `R = A' ×_C B'`.
- `hb`: `b` is surjective, and `hn`: the kernel of `b` is nilpotent.

For a `Λ`-algebra `B`, write `P_B` for the self-product
`(mumfordProduct (abelian A (algebraOver f B))).left` over the test object
`Spec B → Spec Λ → S`.

## Declarations

### `exists_squareExtension`

Given a line bundle `D` on `P_{A'}`, a line bundle `L` on `P_{B'}`, and an isomorphism `φ` from
the pullback of `L` along `productMap A (algHomOver f b)` to the pullback of `D` along
`productMap A (algHomOver f a)`, there is a line bundle `E` on `P_R` with
`(LineBundle.pullback (productMap A (algHomOver f p))).obj E ≅ D`.

Proof. It repeats the proof of `exists_extension` from (F4′), with the general square.

1. Let `g = productStructure A f`, the flat structure map of the self-product over `f`, and
   `θ_B = affineComparison A f B` for a `Λ`-algebra `B`. Both come from
   `TwoAxisClassArtinianLiftingProof`. `θ_B` is the isomorphism from `P_B` to the base change
   of the source of `g` to `Spec B`.
2. The published `FlatInfinitesimalGluing.affineSquareComparison_isEquivalence g p q a b hsq
   hb hn` makes the comparison functor `PicardGroupoid.affineSquareComparison g p q a b hsq`
   an equivalence. Its target is the category of square gluing data
   (`PicardGroupoid.SquareGluingData`) for the base changes along `a` and `b`.
3. The gluing datum `Dat` consists of:
   - left bundle `(inv θ_{A'})^* D` and right bundle `(inv θ_{B'})^* L`;
   - an isomorphism `e` between their pullbacks to the base change over `C`. It is the
     composite of
     - `LineBundle.pullbackCompEqIso` along `inv_affineComparison_naturality` for `a`,
     - the inverse of `pullbackCompEqIso` along `inv θ_C ≫ productMap A (algHomOver f a)`,
     - the pullback of `φ.symm` along `inv θ_C`,
     - `pullbackCompEqIso` along `inv θ_C ≫ productMap A (algHomOver f b)`,
     - the inverse of `pullbackCompEqIso` along `inv_affineComparison_naturality` for `b`.
4. Essential surjectivity gives a bundle `Z` on the base change of `g` to `Spec R`, with an
   isomorphism `eZ` from its comparison image to `Dat`. The left component `eZl` of `eZ`
   identifies the pullback of `Z` along the base change of `p` with `(inv θ_{A'})^* D`.
5. Take `E = θ_R^* Z`. The isomorphism `(productMap A (algHomOver f p))^* E ≅ D` is the
   composite of:
   - `pullbackCompEqIso` along `affineComparison_naturality A f p`;
   - the inverse of `pullbackCompEqIso` along
     `θ_{A'} ≫ (relativeSpace g).map (affineBaseMap p)`;
   - the pullback of `eZl` along `θ_{A'}`;
   - `pullbackCompEqIso` along `θ_{A'} ≫ inv θ_{A'} = 𝟙` (`IsIso.hom_inv_id`);
   - `LineBundle.pullbackId`.

### `classes_squareGluing`

Under the same hypotheses, let `x` be a class over `algebraOver f A'` and `y` a class over
`algebraOver f B'` with
`classesPullback A (algHomOver f b) y = classesPullback A (algHomOver f a) x`. Then there is a
class `z` over `algebraOver f R` with `classesPullback A (algHomOver f p) z = x`.

Proof. It repeats the proof of `classPresheaf_artinianLifting` from (F4′).

1. Choose representatives `D₀` of `x` and `L'` of `y`.
2. By definition of `classesPullback`, the hypothesis equates the classes of
   `(relativePullback A (algHomOver f b)).obj L'` and
   `(relativePullback A (algHomOver f a)).obj D₀`. `Quotient.exact` gives an isomorphism `φ`
   of rigidified bundles.
3. Forgetting rigidifications, `exists_squareExtension` applied to the underlying bundles and
   to `φ` gives `E₀` on `P_R` and `e₀ : (productMap A (algHomOver f p))^* E₀ ≅ D₀`.
4. `LineBundle.twoAxisNormalizedBundleRigidification pullbackTensorComparisonIsIso` gives a
   rigidification `ρ` of the normalization of `E₀`, which has trivial restrictions to both
   axes.
5. `LineBundle.twoAxisNormalizedBundleRestrictionIso` gives an isomorphism of carriers `eN`
   between the restriction of the normalized bundle along `p` and `D₀`. Its inputs are:
   - `e₀`;
   - the axis squares `productMap_fst`, `productMap_snd`, `first_naturality` and
     `second_naturality`;
   - the axis trivializations `D₀.obj.rigidification.first.symm` and `.second.symm`.
6. The witness is the class of `ofLineBundle _ ρ`. Its restriction along `p` is the class of
   `(relativePullback A (algHomOver f p)).obj (ofLineBundle _ ρ)`.
   `nonempty_iso_of_carrierIso` upgrades `eN` to an isomorphism of rigidified bundles, and
   `Quotient.sound` concludes.

## Dependencies and provenance

The module imports `Langlands.AlgebraicGeometry.Picard.TwoAxisClassArtinianLiftingProof`, the
(F4′) proof written for this task, for `productStructure`, `affineComparison` and their
naturality lemmas. The other ingredients are published in the Library:
`FlatInfinitesimalGluing.affineSquareComparison_isEquivalence`, `PicardGroupoid`,
`LineBundle.twoAxisNormalizedBundle*` and `nonempty_iso_of_carrierIso`. The statement is
internal to this proof and has no literature counterpart. It is the formal gluing step used
for (F7).
