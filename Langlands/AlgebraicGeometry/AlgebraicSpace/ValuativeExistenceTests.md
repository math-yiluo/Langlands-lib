# Spectra of algebras over a valuation ring as test schemes

Author: Worker 198.

Helper module for the proof of `SpaceValuativeExistenceStatement` (Stacks Project, Lemma
67.42.3, Tag 0A3Y, (1) ⇒ (3)), given in `SpaceValuativeExistenceProof.lean`. It contains no
statement from the literature. It sets up the test schemes `Spec R` for `A`-algebras `R`, the
equalizer ideals that separatedness provides, and the étaleness of equalizer loci over an étale
chart.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistence`. Fix a scheme `S`, a
commutative ring `A` and a morphism `s : Spec A ⟶ S`. Nothing about `A` is assumed in this
module.

Test schemes:

- `algTest s R` (abbreviation): for an `A`-algebra `R`, the object `Spec R` of `Over S` with
  structure morphism `Spec R ⟶ Spec A` followed by `s`. For `R = K` this is exactly the object over which
  the section `x` of `SpaceValuativeExistenceStatement` lives.
- `algTestMap s φ : algTest s R' ⟶ algTest s R` for an `A`-algebra map `φ : R → R'` (it is
  `Spec.map φ`), and `algTestBase s R : algTest s R ⟶ Over.mk s` (it is `Spec` of
  `algebraMap A R`). `algTestBase s K` is the morphism `Over.homMk (Spec.map ...) rfl` of the
  statement.
- `algTestMap_left`, `algTestMap_comp`, `algTestMap_base`: functoriality and compatibility with
  the base.
- `isPullback_algTest`: `Spec (R ⊗[A] R')` with the two maps induced by `includeLeft` and
  `includeRight` is the fibre product of `Spec R` and `Spec R'` over `Spec A`, in `Over S`. It is
  Mathlib's pushout square of commutative rings `CommRingCat.isPushout_tensorProduct`, turned
  into a pullback of schemes by `isPullback_SpecMap_of_isPushout` and lifted along the faithful
  functor `Over.forget S`, which reflects these pullbacks (`IsPullback.of_map_of_faithful`).
- `exists_comp_mk_iff`: an `A`-algebra map `ψ : R → R'` factors, on spectra, through
  `Spec (R ⧸ I) ⟶ Spec R` exactly when `I ≤ ker ψ`. One direction uses `Spec.preimage` and the
  injectivity of `Spec.map`; the other is `Ideal.Quotient.liftₐ`.
- `mono_algTestMap_mk`: `Spec (R ⧸ I) ⟶ Spec R` is a monomorphism in `Over S` (a closed
  immersion is a monomorphism of schemes, and `Over.forget S` reflects monomorphisms).
- `map_comp_symm`: restriction of a section `χ` along `k` corresponds, under Yoneda, to
  precomposition with `h_k`.

Separatedness, for a morphism `f : X ⟶ Y` of algebraic spaces with `IsSeparatedMorphism f`:

- `exists_representsEqualizer`: for two sections `ξ₁ ξ₂` of `X` over `U` with the same image
  under `f`, there is a closed immersion `ι : Z ⟶ U` with `RepresentsEqualizer ι ξ₁ ξ₂`: a
  morphism `k : T ⟶ U` factors through `ι` iff `ξ₁|_k = ξ₂|_k`. `Z` is the pullback of the
  relative diagonal `X ⟶ X ×_Y X` (a representable closed immersion, by separatedness) along
  `(ξ₁, ξ₂) : h_U ⟶ X ×_Y X`. The proof follows the published
  `exists_representsEqualizer_of_relative_diag` (`DiagonalEqualizer.lean`, absolute diagonal),
  written out for the relative diagonal.
- `exists_ideal_representsEqualizer`: for `U = Spec R`, the closed immersion is
  `Spec (R ⧸ I) ⟶ Spec R` for an ideal `I` of `R` (Mathlib's `IsClosedImmersion.Spec_iff`,
  transported to `Over S` with `Over.isoMk`).
- `pullback_eq_iff_le_ker`: in ring terms, for such an ideal `I` and every `A`-algebra map
  `ψ : R → R'`, the restrictions of `ξ₁` and `ξ₂` along `Spec ψ` agree iff `I ≤ ker ψ`.

Charts of the base change, for `f : X ⟶ Y` and a section `y` of `Y` over `Spec A`:

- `baseChange s f y`: the presheaf `X ×_Y h_{Spec A}`, the fibre product of `f` and the
  morphism `h_{Spec A} ⟶ Y` given by `y`.
- `zOf s f y χ t h`: the morphism `h_T ⟶ X ×_Y h_{Spec A}` given by a section `χ` of `X` over
  `T`, a morphism `t : T ⟶ Spec A` and the compatibility `f(χ) = y|_t`; `zOf_fst` and `zOf_snd`
  compute its two projections.
- `etale_of_chart`: let `ξ` be a section over `Spec P` with `f(ξ) = y|_P` such that the chart
  `zOf ξ : h_{Spec P} ⟶ X ×_Y h_{Spec A}` is étale (`IsEtale`), and let `χ` be a section over
  `Spec R` with `f(χ) = y|_R`. If the ideal `I` of `R ⊗[A] P` cuts out the locus where the
  pullbacks of `χ` and `ξ` agree, then `Spec ((R ⊗[A] P) ⧸ I) ⟶ Spec R` is étale. The square
  formed by this map, `Spec ((R ⊗[A] P) ⧸ I) ⟶ Spec P`, `zOf ξ` and `zOf χ` is a pullback
  square of presheaves; this is checked on elements with the published
  `isPullback_of_elements` (`ExtensionProduct.lean`), using `isPullback_algTest` and
  `RepresentsEqualizer`. The published `IsEtale.projection` then shows the projection is
  étale.
