# Étale classifying neighbourhoods for homomorphisms from a finite diagonalizable group

This module is an internal helper for the étale-local splitting of groups of
multiplicative type (Conrad, *Reductive group schemes*, Appendix B, B.3.4). Its main result
is `exists_etale_classifying`. It turns a homomorphism `D(A) → G` defined after a faithfully
flat base change into one defined over an étale neighbourhood. It uses the étale scheme of
homomorphisms from `MultiplicativeTargetEtale`. The argument is derived and does not follow
a specific text.

## Flatness over an étale target (section `Flatness`)

* `lfp_isMultiplicative`: morphisms locally of finite presentation contain identities and
  are closed under composition, as a Mathlib `MorphismProperty.IsMultiplicative` instance.
  Mathlib provides composition but no identity instance.
* An instance `HasOfPostcompProperty (Flat ⊓ LocallyOfFinitePresentation) Etale`. By
  Mathlib's `hasOfPostcompProperty_iff_le_diagonal`, it suffices that the diagonal of an
  étale morphism is flat and locally of finite presentation. That diagonal is an open
  immersion, since étale morphisms are formally unramified and locally of finite type.
* `flat_lfp_of_comp_etale`: if `p` is étale and `c ≫ p` is flat and locally of finite
  presentation, then so is `c`.

## The universal homomorphism (section `Universal`)

* `sourceModelIso R A : D_{Spec R}(A) ≅ hopfGroup R R[A]` comes from the published
  `Diagonalizable.hopfSpecIso` and `Diagonalizable.relativeModelIso`.
* `universalHom G A` takes an affine group `G` over `Spec R` of finite presentation and a
  finite abelian group `A`. It is the published `universalFamily` of the Hopf-point algebra
  `HomAlgebra R 𝒪(G) R[A]`, transported along `sourceModelIso` and the published
  `coordinateIso G`. The result is a family of homomorphisms `D(A) → G` over
  `specOver R (HomAlgebra R 𝒪(G) R[A])`.
* `isUniversal_universalHom`: this family is universal (published
  `isUniversal_universalFamily` and `IsUniversal.transport`).
* `etale_specOver_hom`: `Spec P → Spec R` is étale when `P` is an étale `R`-algebra.

## Coherence (section `Coherence`)

* `diagonalizableBaseChangeIso_eq`: the published base-change isomorphism
  `diagonalizableBaseChangeIso b A : (D_S(A))_{S'} ≅ D_{S'}(A)` is, by definition, the
  canonical comparison `Descent.pullbackComparison` of iterated base changes from
  `Spec ℤ`.
* `diagonalizableBaseChangeIso_comparison`: let `q : U ⟶ X`, `f : X ⟶ S` and `r : U ⟶ S`
  with `q ≫ f = r`. Then base-changing `diagonalizableBaseChangeIso f A` along `q`, followed
  by the comparison `(D_S(A))_{X,U} ≅ (D_S(A))_U` and then
  `diagonalizableBaseChangeIso r A`, gives `diagonalizableBaseChangeIso q A`. The proof
  compares both sides after the projections of the pullback: the first projection through
  the published `pullbackComparison_hom_fst`/`_inv_fst` and `baseChange_map_left_fst`, the
  second through the structure maps.

## The classifying neighbourhood (section `Classifying`)

* `flat_specBase`, `lfp_specBase`, `surjective_specBase`: `Spec R' → Spec R` is flat,
  locally of finite presentation, or surjective if `R'` is a flat, finitely presented, or
  faithfully flat `R`-algebra, respectively.
* `exists_etale_classifying` (main theorem). Hypotheses:
  * `R → R'` faithfully flat and of finite presentation;
  * `G` affine over `Spec R`, with structure map locally of finite presentation;
  * `ψ : G_{R'} ≅ D_{R'}(Λ)` for some abelian group `Λ`;
  * `A` a finite abelian group;
  * `φ₀ : D_{R'}(A) → G_{R'}` any homomorphism over `Spec R'`.

  Then there are a scheme `X`, an étale `f : X ⟶ Spec R`, a surjective flat morphism
  `q : Spec R' ⟶ X` locally of finite presentation with `q ≫ f = Spec R' → Spec R`, and a
  homomorphism `σ : D_X(A) → G_X`. Base-changing `σ` along `q` and identifying both sides
  with the canonical isomorphisms gives `φ₀`. Precisely,
  `(diagonalizableBaseChangeIso q A).inv ≫ (baseChange q).map σ ≫
  (pullbackComparison f q _ hq G).hom = φ₀`.

  Proof:
  1. Let `Y = Spec HomAlgebra R 𝒪(G) R[A]`. It is étale over `Spec R` by the published
     `etale_homAlgebra`, which uses `ψ`.
  2. Universality of `universalHom` gives the classifying morphism
     `c : Spec R' ⟶ Y` of `φ₀`.
  3. Since `c ≫ (Y → Spec R)` is `Spec R' → Spec R`, which is flat and locally of finite
     presentation, `c` is too (`flat_lfp_of_comp_etale`).
  4. So `c` is open (Mathlib's `isOpenMap_of_generalizingMap` and
     `Flat.generalizingMap`). Take `X` to be the open image `O` of `c` and `f` the
     composite `O ⟶ Y ⟶ Spec R`, which is étale.
  5. Let `q` be the factorization of `c` through `O`. It is surjective by construction. It
     is flat and locally of finite presentation by the postcomposition property applied
     to the open immersion `O ⟶ Y`.
  6. Let `σ` be the restriction of the universal homomorphism to `O`
     (`evaluate`), composed with `diagonalizableBaseChangeIso`.
  7. The identity holds because evaluation is functorial (`evaluate_comp`), because
     evaluation is base change conjugated by the comparisons (`Descent.pullHom`), and by
     `diagonalizableBaseChangeIso_comparison`.

The universe of all rings, groups and schemes is the fixed universe `u`.
