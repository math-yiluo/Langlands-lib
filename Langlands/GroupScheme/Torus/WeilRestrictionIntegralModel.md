# Integral models of Weil restrictions of the multiplicative group

This internal construction and its compatibility lemmas use the existing
Library constructions of `WeilGm.groupScheme`, `algebraBaseChangeIso`,
`congrIso`, and `IntegralModel`. They supply the general integral-point
calculation needed for the torus Iwahori connected-image proof. They introduce
no assertion from an external source.

All types lie in an arbitrary universe `u`. Let R be a commutative domain,
K its fraction field, B₀ a commutative R-algebra that is finite and projective
as an R-module, and B a finite commutative K-algebra. Given a K-algebra
isomorphism

`e : K ⊗[R] B₀ ≃ₐ[K] B`,

`integralModel R K B₀ B e` is the existing Weil restriction
`Res_{B₀/R} G_m` as an integral model of `Res_{B/K} G_m`. Its generic-fibre
identification first uses `algebraBaseChangeIso` and then `congrIso e`.
The structural morphism is affine because it is induced by a ring map on
spectra. The published `WeilGm.smooth` theorem supplies smoothness, and hence
flatness and local finite type, as required by `IntegralModel`.
`integralModel_isSmooth` records the extra smoothness property. No geometric
connectedness is asserted for an arbitrary B₀.

The section comparisons are also available over general commutative bases.
`selfSectionsAlgEquiv A` promotes the canonical ring equivalence
Γ(Spec A) ≃ A to an A-algebra equivalence for the identity test scheme.
`sectionTensorEquiv A B` then identifies B ⊗[A] Γ(Spec A) with B. On a pure
tensor it sends b ⊗ r to ΓSpecIso(r) • b, as recorded by
`sectionTensorEquiv_tmul`. Composing its map on units with the existing
`pointsEquiv` gives `sectionUnitsEquiv A B`, a multiplicative equivalence
between integral sections and Bˣ for a finite projective B.

For a field k, `rationalUnitsEquiv_eq_sectionUnitsEquiv` proves that this
comparison agrees with the existing `rationalUnitsEquiv k B`. The proof uses
`Corepresented.map_affineSectionsIso_pointsEquiv` to relate affine coordinates
to global-section coordinates, then naturality along the canonical
identity-test isomorphism. Tensor induction reduces the remaining equality to
the fact that this test isomorphism has identity underlying scheme map.

`rationalUnitsEquiv_integralPointMap` computes the actual integral-point map:

`(rationalUnitsEquiv K B (M.integralPointMap x) : B)`
`  = e (1 ⊗ₜ (sectionUnitsEquiv (CommRingCat.of R) B₀ x : B₀))`,

where M is the model above. Its proof expands the supplied generic-fibre
identification and uses the point formulas for `congrIso` and
`algebraBaseChangeIso`. The pullback-point comparison for
`baseChangeSectionHom` gives restriction of the original section, and
`pointsEquiv_naturality` describes its effect on the right tensor factor.
Tensor induction finishes the calculation: on a pure tensor, naturality of
ΓSpecIso identifies restriction of a global function with its image under
R → K; the scalar-tower identity moves that scalar between the tensor factors.
Additivity handles sums.

Finally, `mem_integralModel_integralPoints_iff` states the exact image
characterization, using the existing `rationalUnitsEquiv`:

`y ∈ M.integralPoints ↔`
`  ∃ u : B₀ˣ, (rationalUnitsEquiv K B y : B) = e (1 ⊗ₜ (u : B₀))`.

The forward implication takes the unit corresponding to an integral section
and applies the map formula. The reverse implication takes the inverse image
of the supplied unit under `sectionUnitsEquiv`; the map formula and
injectivity of `rationalUnitsEquiv` show that its generic point is y.
The result uses the image definition of integral points and does not require
an additional injectivity hypothesis on the integral-point map.
