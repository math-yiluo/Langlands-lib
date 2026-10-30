# Degree-one cohomology of a product over a field is detected on the two axes: proof

Author: Worker 727. The fibrewise branch was assigned by Worker 606, first executor of task
`eab37f2b-d9cf-40e4-86ad-492608a9c630`.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement.{u}` from
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement`, which it imports
unchanged.

## Main result

`Langlands.AlgebraicGeometry.Picard.fieldTwoAxisH1Injectivity` is the theorem

```lean
theorem fieldTwoAxisH1Injectivity : FieldTwoAxisH1InjectivityStatement.{u}
```

for an arbitrary universe `u`. Unfolded: for `K : CommRingCat.{u}` with `IsField K`, smooth
proper geometrically connected `X Y : Over (Spec K)` with rational points `x₀`, `y₀`, any fibre
product `P` with projections `p₁`, `p₂` (`hP : IsPullback p₁ p₂ X.hom Y.hom`), the axes
`i₁ = hP.lift (𝟙 X.left) (X.hom ≫ y₀.left)` and `i₂ = hP.lift (Y.hom ≫ x₀.left) (𝟙 Y.left)`,
`O` the structure sheaf of `P` and `H = DerivedSections.relativeCohomology (p₁ ≫ X.hom) 1`:
every `c : H.obj O` with `H(η₁) c = 0` and `H(η₂) c = 0`, where `ηⱼ` is the unit
`O ⟶ iⱼ_* iⱼ^* O` of `Scheme.Modules.pullbackPushforwardAdjunction iⱼ`, is zero.

The theorem uses no hypothesis beyond the statement's. Smoothness and geometric connectedness
enter only through `H⁰(X, 𝒪_X) = K` and `H⁰(Y, 𝒪_Y) = K`; properness gives quasi-compactness
and separatedness.

## Modules used

New helper modules, each with its own Markdown:

- `Langlands.Algebra.TensorDegreeOneKunneth`: the degree-one Künneth lemma
  `exists_eq_of_degreeOne` for tensor products of two-term complexes over a field.
- `Langlands.AlgebraicGeometry.Modules.CechDegreeOne`: `exists_cocycle` (classes in `H¹` of a
  Čech-acyclic module as Čech `1`-cocycles on an affine cover, compatible with module maps, and
  zero when the cocycle is a coboundary), `map_unitToPushforwardUnit_eq_zero`, and the instance
  `isQuasicoherent_unit`.
- `Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.ProductCover`: sections of `P`
  over products of affine opens as tensor products (`tensorFam`, `tensorFam_bijective`),
  `prodOpen`, `isAffineOpen_prodOpen`, `iSup_prodOpen_eq_top`, Čech `0`-cocycles of `X` are
  constants (`exists_eq_smul_one_of_cechD_eq_zero`), and the axis compatibilities.
- `Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.Core`:
  `exists_coboundary_of_axes`, the Čech-cochain version of the theorem.

From the Library it uses `AffineVanishing.isCechAcyclic_of_isQuasicoherent` (module
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof`),
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` (the proof of
`SmoothProperConnectedGlobalFunctions`, Stacks 0E0L: `p.app W` is an isomorphism for every
smooth proper geometrically connected `p : X ⟶ S` and every open `W` of `S`), and
`SmoothProperConnectedGlobalFunctionsProof.secHom`.

## Route of the proof

1. **Finite affine covers** (`exists_affineCover`). A proper morphism to the affine `Spec K` is
   quasi-compact and separated, so `X.left` is compact and covered by finitely many affine opens
   `U i` (Mathlib's `isCompact_iff_finite_and_eq_biUnion_affineOpens`). Separatedness makes the
   diagonal affine, so the intersections `U i ⊓ U k` are affine
   (`isAffineHom_diagonal_iff`). Likewise `V j` for `Y.left`.
2. **The product cover.** `Z (i, j) = prodCover p₁ p₂ U V (i, j) = p₁⁻¹ U i ⊓ p₂⁻¹ V j`. These
   opens are affine (`isAffineOpen_prodOpen`) and cover `P` (`iSup_prodOpen_eq_top`).
3. **A cocycle representative.** The structure sheaf is quasi-coherent
   (`isQuasicoherent_unit`), hence Čech-acyclic. `CechDegreeOne.exists_cocycle` for
   `f = p₁ ≫ X.hom` gives a cocycle `z` on the cover `Z` such that `c = 0` as soon as `z` is a
   coboundary, and `u z` is a coboundary for every module map `u` with `H¹(u) c = 0`.
4. **The axis hypotheses.** By `map_unitToPushforwardUnit_eq_zero`, `H(ηⱼ) c = 0` implies that
   `c` is killed by the Library's `unitToPushforwardUnit iⱼ : 𝒪_P ⟶ iⱼ_* 𝒪`, whose sections are
   the ring maps `iⱼ.app`. So step 3 gives, for `j = 1, 2`, cochains `gⱼ` with
   `iⱼ^♯ (z a b) = gⱼ b| - gⱼ a|`.
5. **Rational points and global functions.** The points `x₀.left`, `y₀.left` are sections of
   the structure maps, and they lie in some `U i₀` and `V j₀` (`exists_top_le_preimage`: the
   spectrum of a field has exactly one point). Every global function on `X.left` comes from `K`
   (`surjective_secHom_top`, from `smoothProperConnectedGlobalFunctions` with `S = Spec K` and
   `W = ⊤`: `secHom X.hom ⊤` is `(Scheme.ΓSpecIso K).inv ≫ X.hom.appTop`, a composite of
   isomorphisms); likewise for `Y`.
6. **Conclusion.** `exists_coboundary_of_axes` (module `Core`, with the `K`-algebra structures
   `(secHom X.hom W).hom.toAlgebra` on sections) shows that `z` is a coboundary. The
   cocycle and coboundary conditions of `CechDegreeOne` and the hypotheses of `Core` agree by
   definitional unfolding (`Cech.res` on the presheaf of `O` is restriction of sections of `P`).
   By step 3, `c = 0`.

The source argument (Stacks 0BF3, citing Künneth 0BED) computes
`H¹(P, 𝒪) = H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` and observes that the axis restrictions realise this
decomposition. The Lean proof does not construct the Künneth isomorphism or restriction maps on
the cohomology of `X` and `Y`. It works with one Čech `1`-cocycle on the product cover and needs
only the degree-one part of the Künneth argument (module `Core`).

## Auxiliary results

All in namespace `Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity`:

- `exists_affineCover p`: for `p : X ⟶ Spec R` quasi-compact and separated, a finite type
  `I : Type u` and affine opens `U : I → X.Opens` with affine pairwise intersections covering
  `X`.
- `exists_top_le_preimage hR x hU`: for `R` a field, `x : Spec R ⟶ X` and a cover `U` of `X`,
  `⊤ ≤ x ⁻¹ᵁ U i` for some `i`.
- `surjective_secHom_top p`: for `p : X ⟶ Spec R` smooth, proper and geometrically connected,
  `(secHom p ⊤).hom` is surjective.

## Original source

The Stacks Project, More on Morphisms, proof of Lemma 0BF3 (`lemma-pic-of-product`,
`more-morphisms.tex` lines 9634-9650 of the registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`): "By Künneth the map
`H¹(X_s ×_{Spec κ(s)} Y_s, 𝒪) → H¹(X_s, 𝒪) ⊕ H¹(Y_s, 𝒪)` is injective". Künneth is Stacks,
Varieties, Lemma 0BED (`lemma-kunneth`, `varieties.tex` lines 5441-5630 of the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, same commit). The statement's Markdown
records the errata check for both tags and explains how the Lean statement's unit maps relate to
the restriction maps of the source.
