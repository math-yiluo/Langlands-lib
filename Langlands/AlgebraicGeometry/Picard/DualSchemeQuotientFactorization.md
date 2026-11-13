# Morphisms from affine schemes to the chosen dual factor through finitely presented quotients

Author: Worker 1407.

Module `Langlands.AlgebraicGeometry.Picard.DualSchemeQuotientFactorization` shows that the
Library's chosen dual `dualScheme A hA`, for an abelian scheme `A` over an arbitrary affine base
`Spec R`, is locally of finite presentation. No noetherian hypothesis is needed. It follows the
published `DualSchemeSubalgebraFactorization` module (Worker 3643). That module's
finitely generated subalgebras of `B` are replaced by quotients `D ⧸ J` by finitely generated
ideals `J ≤ I`. Only the universal property recorded in `HasDualScheme` is used. All results are
internal and derived from published Library theorems and the helper modules
`LineBundleQuotientDescent` and `QuotientFactorizationFinitePresentation`. No representability
theorem from the literature is assumed.

## `exists_lineBundle_quotient`

Let `f : X ⟶ Spec R` be quasi-compact and quasi-separated, `D` an `R`-algebra and `I` an ideal
of `D`. Let `M` be a line bundle on `(relativeSpace f).obj (affineBase R (D ⧸ I))`, the fibre
product of `Spec (D ⧸ I)` and `X` over `Spec R`. Then there are a finitely generated `J` with
`hJ : J ≤ I` and a line bundle `L` on the total space over `Spec (D ⧸ J)` such that the pullback
of `L` along `(relativeSpace f).map (affineQuotientMap hJ)` is isomorphic to `M`.

Proof. This mirrors the published `PicardGroupoid.exists_affineFamily_subalgebra`.
`exists_lineBundle_quotient_descent` applies to the pullback square of the chosen fibre product.
It gives `J` and `M₀` on `pullback f (Spec (D ⧸ J) → Spec R)`. Let `c` be the total-space map
followed by `relativeSpaceSymmetry`. Its two projections are as required (`hc₁`, `hc₂`, from
`relativeSpace_map_snd` and the naturality of `relativeProjection`). Take `L` to be the pullback
of `M₀` along the symmetry isomorphism. The asserted isomorphism is the pullback composition
isomorphism followed by the descent isomorphism.

## `exists_rigidifiedFamily_of_lineBundle`

Let `A` be an abelian scheme over any `S`, `q : T ⟶ T₁` a morphism in `Over S` and `F` a
rigidified family over `T`. Let `L₁` be a line bundle on the total space over `T₁` whose pullback
along `(relativeSpace A.X.hom).map q` is isomorphic to the line bundle underlying `F`. Then there
is a rigidified family `F₁` over `T₁` such that `classesPullback q (classOf F₁) = classOf F`.

Proof. This is the normalization argument of the published `exists_rigidifiedFamily_subalgebra`,
written for an arbitrary `q`. Let `c` be the total-space map, `ε, ε₁` the relative unit sections
and `p, p₁` the relative projections, so that `ε ≫ c = q ≫ ε₁` and `c ≫ p₁ = p ≫ q`.
`LineBundle.normalize` produces `F₁` with underlying bundle `L₁ ⊗ p₁^*(ε₁^* L₁)⁻¹`. In the scheme
Picard group, the class of its pullback along `c` is `[L₀] − p^*(ε^*[L₀])`, where `L₀` underlies
`F`. The rigidification of `F` makes `ε^*[L₀] = 0`, so the class is `[L₀]`. Finally,
`RigidifiedLineBundle.nonempty_iso_of_forget_iso` upgrades the isomorphism of underlying bundles
to one of rigidified families.

## `exists_rigidifiedFamily_quotient`

For `A` over `Spec R`, every rigidified family `F` over `affineBase R (D ⧸ I)` is, up to class,
the pullback along `affineQuotientMap hJ` of a rigidified family over `affineBase R (D ⧸ J)`, for
some finitely generated `J` with `hJ : J ≤ I`. This combines the two results above. `A.X.hom` is
quasi-compact and quasi-separated by the Library's instances for abelian schemes.

## `exists_dualScheme_quotient_factorization`

Every arrow `x : affineBase R (D ⧸ I) ⟶ dualScheme A hA` factors as `affineQuotientMap hJ₂ ≫ y`
with `J₂ ≤ I` finitely generated.

Proof. This has the same structure as `exists_dualScheme_subalgebra_factorization`. Pull back the
Poincaré family along `x`; the result is Picard-zero (`picardZeroPullback`). Descend it to `F₁`
over `D ⧸ J` and take the Picard-zero open locus `U` of `F₁` (`exists_isPicardZeroOpenLocus`). The
image of `Spec (D ⧸ I)` lies in `U`. `exists_affineQuotientMap_range_subset` gives a finitely
generated `J₂` with `J ≤ J₂ ≤ I` whose image lies in `U`. Hence the class `q₂` of the pullback of
`F₁` to `Spec (D ⧸ J₂)` is Picard-zero. Put `y = dualClassify A hA _ ⟨q₂, _⟩`. Then
`dualClassify_pullback`, `classifyingMap_comp` and `affineQuotientMap_comp` identify the class
classified by `affineQuotientMap hJ₂ ≫ y` with that of `F`, and `dualClassify_unique` concludes.

## `dualScheme_locallyOfFinitePresentation_affine`

For every ring `R`, every abelian scheme `A` over `Spec R` and every `hA : HasDualScheme A`, the
morphism `(dualScheme A hA).hom` is locally of finite presentation.

Proof. The published `dualScheme_locallyOfFiniteType` gives local finite type. The factorization
above is `HasQuotientFactorization (dualScheme A hA)`. Then apply
`locallyOfFinitePresentation_of_quotientFactorization`.
