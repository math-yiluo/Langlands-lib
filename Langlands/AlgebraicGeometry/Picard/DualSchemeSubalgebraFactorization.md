# Morphisms from affine schemes to the chosen dual factor through finite stages

Author: Worker 3643.

Module `Langlands.AlgebraicGeometry.Picard.DualSchemeSubalgebraFactorization` shows that
the Library's chosen dual `dualScheme A hA` of an abelian scheme `A` over an affine base
`Spec R` is locally of finite type, and locally of finite presentation when `R` is
noetherian. Only the actual universal property recorded in `HasDualScheme` is used: the
chosen dual classifies Picard-zero classes of rigidified line bundles on every test scheme
over the base (`dualClassify`, `dualClassify_unique`, `dualClassify_pullback`). No
representability theorem from the literature is assumed. All results are internal and
derived from published Library theorems.

## `exists_isPicardZeroOpenLocus`

For an abelian scheme `A` over an arbitrary scheme `S`, every `P : Over S` and every
rigidified family `L : RigidifiedFamily A P`, there is an open `U ⊆ P.left` with
`IsPicardZeroOpenLocus A L U`: for every `T : Over S` and `h : T ⟶ P`, the pulled-back class
is Picard-zero exactly when the image of `h.left` lies in `U`. The proof is the proof of the
published `finiteTypePicardZeroOpenLocus`, which never uses its finite-type hypothesis on the
base: the comparison `exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion`,
applied with the fibrewise criterion `mumfordTrivialLocus` /
`isTranslationInvariant_fibreLineBundle_iff`, followed by the bridge
`isPicardZeroOpenLocus_of_geometricPoints picardZeroGeometricDetection`.

## `exists_rigidifiedFamily_subalgebra`

Let `B` be an `R`-algebra and `F` a rigidified family of `A` over `affineBase R B` (that is,
a line bundle on `Spec B ×_{Spec R} A` with a trivialization of its restriction along the
unit section). Then there are a finitely generated subalgebra `B₁ ⊆ B` and a rigidified
family `F₁` over `affineBase R B₁` whose pullback along `affineSubalgebraMap B₁` has the
same isomorphism class as `F`.

Proof. Write `c` for the map of total spaces over `Spec B → Spec B₁`, `ε, ε₁` for the
relative unit sections and `p, p₁` for the relative projections, so that `ε ≫ c = q ≫ ε₁`
and `c ≫ p₁ = p ≫ q` with `q = Spec B → Spec B₁`.
1. The published `PicardGroupoid.exists_affineFamily_subalgebra` (A is proper, hence
   quasi-compact and quasi-separated) gives `B₁` and a line bundle `L₁` on the total space
   over `Spec B₁` with `c^* L₁ ≅ L₀`, where `L₀` is the line bundle underlying `F`.
2. Normalize `L₁` along `ε₁`: with `N₁ = ε₁^* L₁` and its chosen inverse
   `N₁⁻¹` (`LineBundle.inverse`, with evaluation `tensorInverseIso`),
   `LineBundle.normalize` gives the rigidified family `F₁` with underlying bundle
   `L₁ ⊗ p₁^* N₁⁻¹`.
3. In the scheme Picard group, using `classOf_tensor`, `classOf_inverse`,
   `pullback_lineBundle_classOf`, `Group.pullback_comp` and the two square identities,
   the class of `c^*(L₁ ⊗ p₁^* N₁⁻¹)` equals
   `[L₀] − p^*(ε^*[L₀])`. The rigidification of `F` gives `ε^* L₀ ≅ 𝒪`, so this class is
   `[L₀]`. Hence the underlying line bundles of the pulled-back `F₁` and of `F` are
   isomorphic.
4. `RigidifiedLineBundle.nonempty_iso_of_forget_iso` (the unit section has the retraction
   `p`) upgrades this to an isomorphism of rigidified families, which is the asserted
   equality of classes.

## `exists_dualScheme_subalgebra_factorization`

Every arrow `x : affineBase R B ⟶ dualScheme A hA` factors as
`affineSubalgebraMap B₂ ≫ y` for some finitely generated subalgebra `B₂ ⊆ B` and some
`y : affineBase R B₂ ⟶ dualScheme A hA`.

Proof. Let `F` be the pullback of the Poincaré family along `x`; it is Picard-zero by the
published `picardZeroPullback`. Descend it to `F₁` over `B₁` as above and take the open
locus `U` of `F₁`. Since the pullback of `F₁` to `Spec B` has the class of `F`, the image of
`Spec B` lies in `U`; `exists_affineAlgebraStageMap_range_subset` gives a finitely generated
`B₂ ≥ B₁` whose image lies in `U`, so the class `q₂` of the pullback of `F₁` to `Spec B₂` is
Picard-zero. Put `y = dualClassify A hA _ ⟨q₂, _⟩`. By `dualClassify_pullback`,
`affineSubalgebraMap B₂ ≫ y` classifies the pullback of `q₂` to `Spec B`, which by
`classifyingMap_comp` and `affineAlgebraStageMap_restrict` is the class of `F`; by
`dualClassify_unique` this arrow is `x`.

## `dualScheme_locallyOfFiniteType` and `dualScheme_locallyOfFinitePresentation`

For an abelian scheme `A` over `Spec R` with `hA : HasDualScheme A`, the structure morphism
of `dualScheme A hA` is locally of finite type; if `R` is noetherian it is locally of finite
presentation. These follow from the factorization above and
`locallyOfFiniteType_of_subalgebraFactorization`,
`locallyOfFinitePresentation_of_subalgebraFactorization`. In particular this applies over a
field. These theorems concern affine bases only and do not prove the Library's
`RelativeDualSchemeFinitePresentationStatement` over arbitrary quasi-separated bases.
