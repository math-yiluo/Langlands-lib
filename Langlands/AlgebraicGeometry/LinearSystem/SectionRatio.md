# Ratios of pulled-back line-bundle sections

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.LinearSystemMorphismStatement`. It is internal: it is not a
Library statement and has no literature source of its own. It formalizes the elementary
fact used in the construction of the morphism to projective space (compare Stacks Project, Constructions of Schemes, Section 27.14 "Invertible sheaves and morphisms into Proj", Lemma 27.14.1, tag 01NJ, in the registered source `stacks-very-ampleness-support-2026-10-29`): on the locus where a section `s₀` of a
line bundle generates it, every other section `σ` is a unique function multiple
`σ = r · s₀`. Here this is done after pulling back along an arbitrary morphism `g : T ⟶ X`,
so that the ratio is a global function on `T`. Everything is in the namespace
`Langlands.AlgebraicGeometry.LinearSystem`.

## Algebra of section morphisms and pulled-back sections

For a module sheaf `M` on `X`, Library's `sectionHom M s : 𝒪_X ⟶ M` sends `1` to `s`, and
`pullbackSection f M s` is the pulled-back section along `f : T ⟶ X`.

- `sectionHom_add`, `sectionHom_zero`, `sectionHom_smul`: `sectionHom` is additive, and
  `sectionHom M (r • s)` is multiplication by `r` (Library's `structureMulHom r`) followed by
  `sectionHom M s`. Additivity reuses the published
  `FiniteSectionAvoidance.sectionHom_add`; the other proofs compare
  components using `LineBundleDescent.sectionHom_app`.
- `pullbackSection_add`, `pullbackSection_zero`, `pullbackSectionAddHom`,
  `pullbackSection_sum`: pullback of sections is additive (the pullback functor is additive).
  The zero identity reuses `Langlands.SchemeModule.pullbackSection_zero`
  with the same arguments in the local interface's order.
- `pullbackSection_smul`: `pullbackSection f M (r • s) = f^#(r) • pullbackSection f M s`
  for `r ∈ Γ(X, ⊤)`. The proof uses Library's `pullback_structureEnd_eq_mulHom` (the pullback
  of multiplication by `r` is multiplication by `f^#(r)`).
- `pullbackSection_comp`: for `f : T ⟶ X` and `h : T' ⟶ T`, pulling a section of `M` back
  first along `f` and then along `h` agrees with pulling it back along the composite
  `h ≫ f : T' ⟶ X`, after the canonical isomorphism `pullbackComp h f`. The proof is injectivity
  of `sectionHom` together with the naturality of `pullbackComp` and Library's
  `pullbackUnitComposition`.
- `vanishesAlong_comp`: if `σ` vanishes along `g` (Library's `VanishesAlong L g σ`: the
  pullback of `σ` along `g` is zero), then it vanishes along every composite `h ≫ g`.

## The ratio `sectionRatio`

Let `L` be a line bundle on `X` and `s₀` a global section. Write `U = trivializationOpen L.obj
s₀` for the largest open on which `1 ↦ s₀` is an isomorphism `𝒪 ≅ L`.

- `bijective_sectionHom_pullbackSection`: if `g : T ⟶ X` maps every point into `U`, then the
  pulled-back section `g^* s₀` generates the pulled-back line bundle on all of `T`. That is,
  `a ↦ a • g^* s₀` is a bijection `Γ(T, ⊤) → Γ(T, g^* L)`. The proof uses Library's
  `lineBundlePullbackSectionOpen` (the trivialization open of `g^* s₀` is `g⁻¹ U`),
  `maximalTrivialization` and `LineBundleDescent.trivializesOn_iff_bijective`.
- `sectionHom_app_top`: on global sections, `sectionHom N τ` is `a ↦ a • τ`.
- `sectionRatio L g σ s₀ : Γ(T, ⊤)` is defined for every `g`, by `Classical.epsilon`, as
  some `a` with `a • g^* s₀ = g^* σ`. It is meaningful when `g` lands in `U`; all lemmas
  below assume this.
- `sectionRatio_smul`, `sectionRatio_eq_iff`: `sectionRatio L g σ s₀ • g^* s₀ = g^* σ`, and the
  ratio is the unique such function.
- `vanishesAlong_iff_sectionRatio_eq_zero`: `σ` vanishes along `g` if and only if its ratio is
  zero.
- `sectionRatio_self`, `sectionRatio_add`, `sectionRatio_zero`, `sectionRatio_smul_left`,
  `sectionRatio_sum`: the ratio of `s₀` to itself is `1`, and the ratio is additive and
  satisfies `ratio(r • σ) = g^#(r) * ratio(σ)` for `r ∈ Γ(X, ⊤)`.
- `sectionRatio_comp` (naturality): `sectionRatio L (h ≫ g) σ s₀ = h^#(sectionRatio L g σ s₀)`.
- `sectionRatio_mul`, `isUnit_sectionRatio`: if `g` lands in the trivialization opens of both
  `s₀` and `s₁`, then `ratio(σ, s₁) * ratio(s₁, s₀) = ratio(σ, s₀)`, and `ratio(s₁, s₀)` is a
  unit.
- `vanishesAlong_iff_not_mem`: for a field `K` and a `K`-point `y : Spec K ⟶ X`, `σ` vanishes
  along `y` if and only if the image of the closed point is outside the trivialization open of
  `σ`. If the point is inside, `y^* σ` generates the pulled-back line bundle, so it is nonzero
  because `1 ≠ 0` in `K`. If it is outside, then by Library's
  `lineBundleResidueOpenComparison` the residue section of `σ` at that point is zero. Since `y`
  factors through the residue field of its image point
  (`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`), the pullback along `y`
  is also zero, by `pullbackSection_comp`.
