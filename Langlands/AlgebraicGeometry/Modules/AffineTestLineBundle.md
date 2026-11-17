# Line bundles, global values and trivialization frames for affine test systems

Lean module: `Langlands.AlgebraicGeometry.Modules.AffineTestLineBundle`.

This module builds on `AffineTestRealization`, which gives the realization `E.toModules` of an
affine test system `E` on a scheme `S`, and on `AffineTestComparison`, which gives the frames
`frame a : a^* E.toModules ≅ (E.obj a)^~` and their coherence. No hypotheses on `S` are
imposed.

## Line bundles

- `isLocallyFreeRankOne_toModules`: suppose that for every affine open `U` of `S` the associated
  sheaf `(E.obj hU.fromSpec)^~` on `Spec Γ(S, U)` is locally free of rank one
  (`Picard.IsLocallyFreeRankOne`). Then `E.toModules` is locally free of rank one.
  Proof: around a point `x` choose an affine open `U`. The restriction of `E.toModules` along the
  open immersion `hU.fromSpec` is isomorphic to `hU.fromSpec^* E.toModules ≅ (E.obj hU.fromSpec)^~`,
  using `restrictFunctorIsoPullback` and `frame`. The rank-one locus commutes with restriction
  along open immersions (`rankOneLocus_restrict`).
- `toLineBundle h : Picard.LineBundle S` is the realization with this property.

## Values of global sections on affine tests

For an affine test `a : Spec R ⟶ S`:

- `topEquiv a` is the bijection `topLinear a : E.obj a ≃ Γ((E.pullback a).toModules, ⊤)`.
- `evalTop a s : E.obj a` is the value of a global section `s` of `E.toModules`. It is obtained
  by pulling `s` back along `a`, applying the comparison `a^* E.toModules ⟶ (E.pullback a).toModules`
  and then the inverse of `topEquiv a`. `topLinear_evalTop` records this, and `evalTop_add`
  states additivity.
- **`evalTop_ext`**: for an `R`-algebra `A` and `h : Spec(R → A) ≫ a = b`,
  `evalTop b s = E.ext h (1 ⊗ evalTop a s)`. The proof evaluates `comparison_comp` on pulled-back
  global sections, uses `sectionsEquiv_comparison_app` on the affine opens `⊤`, and uses the
  naturality of `ΓSpecIso`.

## Frames from a trivialization

Let `ψ : 𝒪_S ≅ E.toModules`, and let `generator ψ` be the image of the global section `1`.

- `frameIso a ψ : R^~ ≅ (E.obj a)^~` composes `tildeSelf`, the inverse of the Library's
  `pullbackUnitIso a : a^* 𝒪_S ≅ 𝒪_{Spec R}`, `a^* ψ` and `frame a`.
  `frameIso_hom_app_toOpen_one` says it sends the generator `1` to
  `tilde.toOpen _ ⊤ (evalTop a (generator ψ))`. This uses `tilde_toOpen_one`,
  `pullbackUnitIso_inv_one` (from the adjunction characterization `pullbackUnitAdjunction`) and
  `frame_hom_app_sectionPullbackLE`.
- `tilde_map_trivFrameHom`: the tilde of the map `r ↦ r • evalTop a (generator ψ)` is
  `(frameIso a ψ).hom`. Since `tilde` is fully faithful, this map is bijective
  (`trivFrame_bijective`).
- **`trivFrame a ψ : R ≃ₗ[R] E.obj a`**, `r ↦ r • evalTop a (generator ψ)`. By `trivFrame_ext`,
  `trivFrame b ψ 1 = E.ext h (1 ⊗ trivFrame a ψ 1)` whenever `Spec(R → A) ≫ a = b`.

## Under the Picard hypothesis

Assume every `L : LineBundle S` satisfies `Nonempty (L ≅ LineBundle.trivial S)`, and that the
chart modules satisfy the rank-one hypothesis `h` above.

- `picardTrivialization h hPic : 𝒪_S ≅ E.toModules` is a trivialization chosen from the
  hypothesis applied to `toLineBundle h`.
- `picardFrame h hPic a : R ≃ₗ[R] E.obj a` is `trivFrame` for this trivialization.
  **`picardFrame_ext`** states the coherence: after extending coefficients to the same affine test
  ring, the frame vectors agree, `picardFrame b 1 = E.ext h (1 ⊗ picardFrame a 1)`.

## Provenance

This is an internal construction for the task that builds root-weight line bundles over arbitrary
base schemes. When specialized to the root-weight system, it gives the line bundles `L_α` and the
coherent affine frames under the parent's Picard hypothesis. Mathematically: a quasi-coherent sheaf
that is locally the associated sheaf of a rank-one projective module is a line bundle, and a global
trivialization restricts to compatible trivializations on all affine tests.
