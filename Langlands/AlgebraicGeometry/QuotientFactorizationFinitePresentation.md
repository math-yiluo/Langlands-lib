# Local finite presentation from factorizations through finitely presented quotients

Author: Worker 1407.

Module `Langlands.AlgebraicGeometry.QuotientFactorizationFinitePresentation` proves a criterion
for local finite presentation. Let `P` be a scheme over `Spec R` that is locally of finite type.
Suppose that every morphism over `Spec R` from `Spec (D ⧸ I)` to `P` factors through
`Spec (D ⧸ J)` for some finitely generated ideal `J ≤ I`. Then `P` is locally of finite
presentation over `Spec R`. It is a helper module for the proof of
`Langlands.AbelianScheme.RelativeDualSchemeFinitePresentationStatement`.

This is the affine case of the functorial characterization of local finite presentation:
morphisms out of filtered limits of rings factor through a finite stage; compare EGA IV §8.14.
Here the criterion is restricted to quotient systems and proved directly
by a retract argument. The results are internal and derived; no literature statement is
transcribed.

## `affineQuotientMap` and `affineQuotientMap_comp`

For ideals `J ≤ I` of an `R`-algebra `D`, `affineQuotientMap h` is the arrow
`affineBase R (D ⧸ I) ⟶ affineBase R (D ⧸ J)` in `Over (Spec R)` given by
`Spec (Ideal.Quotient.factor h)`. `affineBase` is the Library's `Over.mk (Spec.map (algebraMap R A))`.
For `K ≤ J ≤ I`, `affineQuotientMap_comp` states that the composite
`affineQuotientMap hJI ≫ affineQuotientMap hKJ` equals `affineQuotientMap (hKJ.trans hJI)`. This
follows from `Ideal.Quotient.factor_comp`.

## `exists_quotient_comap_mem_of_isOpen` and `exists_affineQuotientMap_range_subset`

Let `J ≤ I` with `J` finitely generated, and let `U` be an open subset of `Spec (D ⧸ J)` that
contains the image of `Spec (D ⧸ I)`. Then there is a finitely generated ideal `J'` with
`J ≤ J' ≤ I` such that the image of `Spec (D ⧸ J')` lies in `U`. The second lemma is the same
statement phrased with `affineQuotientMap` and opens of the scheme.

Proof. Write the closed complement of `U` as `V(K)` for an ideal `K` of `D ⧸ J`. The image of `K`
in `D ⧸ I` is the unit ideal; otherwise a maximal ideal containing it would give a point of
`Spec (D ⧸ I)` mapping outside `U`. Choose `d ∈ D` whose class lies in `K` and maps to `1` in
`D ⧸ I`, so `1 − d ∈ I`. Put `J' = J ⊔ (1 − d)`, which is finitely generated and lies in `I`. In
`D ⧸ J'` the class of `d` is `1`. Hence no prime of `D ⧸ J'` contains the image of `K`, and every
point of `Spec (D ⧸ J')` maps into `U`.

## `HasQuotientFactorization`

For `P : Over (Spec R)`, `HasQuotientFactorization P` means the following. For every `R`-algebra
`D` (in the same universe), every ideal `I` of `D` and every `x : affineBase R (D ⧸ I) ⟶ P`, there
are a finitely generated `J` with `hJ : J ≤ I` and `y : affineBase R (D ⧸ J) ⟶ P` such that
`affineQuotientMap hJ ≫ y = x`. This is a helper predicate, not a literature definition.

## `finitePresentation_preimage_of_quotientFactorization`

Assume `HasQuotientFactorization P`. Let `j : Spec C ⟶ P.left` be an open immersion such that the
ring map `φ : R → C` underlying `j ≫ P.hom` is of finite type. Then `φ` is of finite
presentation.

Proof (retract argument).
1. Present `C` as `D ⧸ I` with `D = R[X₁,…,Xₙ]` and `I` the kernel of a surjection, using
   `Algebra.FiniteType.iff_quotient_mvPolynomial''`. Let `e : D ⧸ I ≃ₐ[R] C` be the induced
   isomorphism.
2. The arrow `x : Spec (D ⧸ I) ≅ Spec C → P` factors as `affineQuotientMap hJ ≫ y` with `J`
   finitely generated.
3. The image of `Spec (D ⧸ I)` in `Spec (D ⧸ J)` lies in the open set `y⁻¹(j(Spec C))`. The range
   lemma gives a finitely generated `J₂` with `J ≤ J₂ ≤ I` such that `Spec (D ⧸ J₂) → P` factors
   through `j`, as `g : Spec (D ⧸ J₂) ⟶ Spec C` (`IsOpenImmersion.lift`).
4. Let `ψ : C → D ⧸ J₂` be the ring map of `g`. Since `j` is a monomorphism, `ψ` followed by
   `D ⧸ J₂ → D ⧸ I` is `e⁻¹`. Hence `ρ = e ∘ (D ⧸ J₂ → D ⧸ I)` satisfies `ρ ∘ ψ = id`. Both `ψ`
   and `ρ` are maps of `R`-algebras.
5. `R → D ⧸ J₂` is of finite presentation (`Algebra.FinitePresentation.quotient`). Therefore `ψ`
   is of finite type (`RingHom.FiniteType.of_comp_finiteType`), and `ρ` is of finite
   presentation by `RingHom.FinitePresentation.of_comp_finiteType`, because `ρ ∘ ψ = id`. Hence
   `φ = ρ ∘ (R → D ⧸ J₂)` is of finite presentation.

## `locallyOfFinitePresentation_of_quotientFactorization`

If `P : Over (Spec R)` is locally of finite type and `HasQuotientFactorization P`, then `P.hom`
is locally of finite presentation.

Proof. Local finite presentation is local on the source, so it suffices to check it on the
affine open cover `P.left.affineOpenCover`. On each chart `Spec C`, the composite to `Spec R` is
locally of finite type, so its ring map is of finite type (`HasRingHomProperty.Spec_iff`). The
previous theorem then makes it of finite presentation.
