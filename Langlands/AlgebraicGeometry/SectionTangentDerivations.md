# Tangent sections over a one-point base and point derivations of the stalk

Author: Worker 254.

Module `Langlands.AlgebraicGeometry.SectionTangentDerivations`. This is a
helper for the proof of
`Langlands.Scheme.FieldPointTangentLocalRegularityStatement`, and it is
reusable on its own.

Let `S` be a scheme with one point `pt`, let `X : Over S`, and let
`e : Over.mk (𝟙 S) ⟶ X` be a section. This module identifies the global
sections of the published tangent module
`Langlands.Scheme.tangentAtSection X e`, defined as
`Modules.dual (e^* Ω_{X/S})`, with the point derivations of the actual stalk
`O_{X, e(pt)}` with values in the actual stalk `O_{S, pt}`. Every step is
proved. No comparison, stalk computation or residue-field identification is
assumed.

## Provenance

The construction is derived and internal. Mathematically it is the
identification `T = Hom_{O_{X,x}}(Ω_{X/S,x}, κ(x))` of Stacks Project
Lemma 33.16.4 (Tag 0B2D, registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, `varieties.tex`,
lines 3013–3056). Here it is realised for the published sheaf-theoretic
tangent module, in its equivalent derivation form.

The route differs from Stacks, which uses dual-number points. The steps
below never compute the pullback `e^* Ω` or the stalk of `Ω`. They use the
pullback–pushforward adjunction instead. No dual numbers appear.

## The steps

1. `Langlands.Scheme.Modules.localHomTopEquiv M N : LocalHom M N ⊤ ≃ (M ⟶ N)`
   holds for any scheme. A local morphism over `⊤` lives on the opens over
   `⊤`, and these are all the opens. So it is the same thing as a global
   morphism of module sheaves. `localHomTopEquiv_app` records the components.
2. Mathlib's `Scheme.Modules.pullbackPushforwardAdjunction e.left` gives
   `(e^* Ω ⟶ O_S) ≃ (Ω ⟶ e_* O_S)`.
3. The Library's `Langlands.Scheme.relativeDifferentialsHomEquiv` gives
   `(Ω ⟶ N) ≃ RelativeDerivation X.hom N`.
4. The skyscraper comparison (section `Skyscraper`) works for arbitrary
   `f : Y ⟶ S` and `s : S ⟶ Y`. Write
   `pointModule s = (pushforward s).obj (structureModule S)`.
   - `sectionEquiv s U` identifies the sections of `pointModule s` over `U`
     with `Γ(S, s ⁻¹ᵁ U)`. Its multiplication and restriction lemmas hold
     by `rfl`.
   - `stalkValue pt D U hx a` is `germ_pt (D_U a)`.
   - Using `germ_eq`, `stalkValue_eq_of_germ_eq` shows that it depends only on
     the germ of `a` at `s pt`.
   - `stalkFun` chooses a representative germ (`exists_germ_eq`).
   - `stalkDerivation D` is the resulting point derivation in
     `derivations (baseMap f s pt) (s.stalkMap pt).hom`. Here
     `baseMap f s pt` is `germ ∘ f.app ⊤`. Additivity and the Leibniz rule are
     checked on a common open (`exists_common_germ`, `germ_sectionEquiv_smul`).
   - Assume `[Subsingleton S]`. Then every open of `S` is `⊥` or `⊤`
     (`eq_top_of_mem`, `eq_bot_of_notMem`).
     - `Γ(S, ⊥)` is subsingleton.
     - The germ map `Γ(S, V) → O_{S,pt}` is bijective for `pt ∈ V`
       (`germ_bijective`), with inverse `germInv`.
     - `section_ext` and `pointModule_ext` compare sections through their
       germs.
   - `ofStalkDerivation δ` is the inverse. Its value on `U` is
     `germInv (δ (germ a))` if `s pt ∈ U`, and `0` otherwise.
   - `stalkDerivationEquiv` is the resulting equivalence
     `RelativeDerivation f (pointModule s) ≃ derivations (baseMap f s pt)
     (s.stalkMap pt).hom`.
5. Section `Tangent` composes the steps.
   - `tangentAdjoint X e t : Ω ⟶ pointModule e.left` is the adjoint morphism.
   - `tangentEval X e t U a` is its value on `d a`.
   - `tangentEval_add` holds by `rfl`. So does `tangentEval_smul`, which says
     the value on `c • t` is the value on `t` times the restriction of `c`.
   - `tangentDerivationEquiv X e pt` is the composite equivalence
     `Γ(tangentAtSection X e, ⊤) ≃ derivations (baseMap X.hom e.left pt)
     (e.left.stalkMap pt).hom`.
   - `tangentDerivationEquiv_germ` gives the evaluation formula
     `δ_t (germ_U a) = germ_pt (tangentEval X e t U a)`.
   - `tangentDerivationEquiv_add` and `tangentDerivationEquiv_smul` follow
     from it. The second says the equivalence turns the `Γ(S, ⊤)`-action into
     multiplication by `germ_⊤ c`.
   - `stalkMap_baseMap` uses `e.left ≫ X.hom = 𝟙` (`Over.w e`). It shows that
     `e.left.stalkMap pt ∘ baseMap = germ_⊤`, so the derivations vanish
     exactly on the base.

The source of `e.left` is `(Over.mk (𝟙 S)).left`, which is definitionally `S`.
Lemmas about it are stated with that scheme's presheaf. The local instance
`subsingletonSectionSource` transfers `Subsingleton S` to it.

## Imports

- `Langlands.AlgebraicGeometry.PointTangentSpace` (published, unchanged).
- `Langlands.AlgebraicGeometry.RelativeDifferentialsUniversal` (published,
  unchanged).
- `Langlands.CommutativeAlgebra.PointDerivationCotangent` (new helper, for
  `derivations`).

No existing Library file is changed.
