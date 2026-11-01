# The degeneration isomorphism of the hyperext spectral sequence

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextDegeneration.Statement`
(`HyperextDegenerationStatement`, `HyperextDegeneration.edgeMap`; Worker 3),
`Langlands.Cohomology.HyperextAbutmentFiltration` (`edgeMapAddMonoidHom`;
Worker 61), `Langlands.Cohomology.ExtProjectiveResolution`
(`subsingleton_ext_homology_of_projective`; Worker 61) and
`Langlands.Cohomology.SmoothHyperextSecondPage`, which imports
`Langlands.Cohomology.ExtRightDerived` (`smoothExtAddEquiv`) and
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`). It also uses Mathlib's
`Abelian.Ext.subsingleton_of_injective`.

Let `C` be an abelian category. For an object `K` of its derived category and
an object `W` of `C`, write `W₀` for `W` placed in degree `0` and `H^i` for
the cohomology functor in degree `i`. The edge map
`HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`
sends a morphism to the morphism it induces on `H^{-n}`. Worker 3's
proposition `HyperextDegenerationStatement.{w, w'} C` asserts the following.
If the cohomology of `K` vanishes above some `b`, and
`Abelian.Ext.{w'} (H^k K) W i` is trivial for every `k : ℤ` and every
`i : ℕ` with `0 < i`, then the edge map is bijective for every `n`.

This module **does not prove** `HyperextDegenerationStatement`. It takes the
proposition as an explicit hypothesis `h` and packages the bijective edge map
as an additive isomorphism. It also supplies three ways to discharge the
`Ext` hypothesis.

## Declarations

Section `General` takes an abelian category `C` with objects in `Type u` and
morphisms in `Type v`, and instances `HasDerivedCategory.{w} C` and
`HasExt.{w'} C`. In every declaration below, `hK` is the hypothesis
`∀ i : ℤ, b < i → IsZero (H^i K)`, and `hW` is the hypothesis
`∀ (k : ℤ) (i : ℕ), 0 < i → Subsingleton (Abelian.Ext.{w'} (H^k K) W i)`.
These are exactly the hypotheses of `HyperextDegenerationStatement`.

| Declaration | Statement |
| --- | --- |
| `subsingleton_ext_of_injective K W` | If `W` is injective (`[Injective W]`), then `hW` holds: `Abelian.Ext.{w'} (H^k K) W i` is trivial for every `k` and every `i > 0`. |
| `degenerationAddEquiv h K b hK W hW n` | Given `h : HyperextDegenerationStatement.{w, w'} C`, the additive isomorphism `ShiftedHom K W₀ n ≃+ (H^{-n} K ⟶ W)` whose underlying map is the edge map: Mathlib's `AddEquiv.ofBijective` applied to `edgeMapAddMonoidHom K W n` and the bijectivity `h K b hK W hW n`. A `def`. |
| `degenerationAddEquiv_apply` | `degenerationAddEquiv h K b hK W hW n f = edgeMap K W n f` (a `simp` lemma, by definition). |
| `edgeMap_degenerationAddEquiv_symm_apply` | `edgeMap K W n ((degenerationAddEquiv h K b hK W hW n).symm g) = g` for `g : H^{-n} K ⟶ W` (a `simp` lemma). |
| `degenerationAddEquivOfInjective h K b hK W n` | `degenerationAddEquiv` for injective `W`, with `hW` supplied by `subsingleton_ext_of_injective`. A `def`. |
| `degenerationAddEquivOfProjective h K b hK hP W n` | `degenerationAddEquiv` when every `H^k K` is projective (`hP : ∀ k, Projective (H^k K)`), with `hW` supplied by the Library's `ExtProjectiveResolution.subsingleton_ext_homology_of_projective`. A `def`. |

Section `Smooth` takes a commutative ring `R : Type u`, a topological group
`G : Type u`, and instances `HasDerivedCategory.{w}` and `HasExt.{w'}` for
the category `SmoothRep.{u, u, u} R G` of smooth representations.
`SmoothExt.ext R G V i` is the Library's smooth Ext functor, the `i`-th right
derived functor of equivariant Hom out of `V`.

| Declaration | Statement |
| --- | --- |
| `subsingleton_ext_of_smoothExt R G K W hW` | If `(SmoothExt.ext R G (H^k K) i).obj W` is trivial for every `k : ℤ` and every `i : ℕ` with `0 < i` (`hW`), then `Abelian.Ext.{w'} (H^k K) W i` is trivial for the same `k` and `i`. |
| `smoothDegenerationAddEquiv R G h K b hK W hW n` | Given `h : HyperextDegenerationStatement.{w, w'} (SmoothRep R G)` and the smooth-Ext hypothesis `hW` above, the additive isomorphism `ShiftedHom K W₀ n ≃+ (H^{-n} K ⟶ W)` given by the edge map. A `def`. |

Proofs.

- `subsingleton_ext_of_injective`: write `i = m + 1` and apply Mathlib's
  `Abelian.Ext.subsingleton_of_injective`.
- `edgeMap_degenerationAddEquiv_symm_apply` is `AddEquiv.apply_symm_apply`.
- `subsingleton_ext_of_smoothExt`: the Library's
  `ExtRightDerived.smoothExtAddEquiv R G (H^k K) W i` is an additive
  equivalence from the smooth Ext group to Mathlib's `Ext`, for any instance
  `HasExt.{w'}`. Its inverse is injective into a trivial group
  (`Function.Injective.subsingleton`).
- The other `def`s apply `degenerationAddEquiv` to the indicated `hW`.

## Provenance and interpretation

The definitions are ours, assembled from Mathlib and the Library.
`HyperextDegenerationStatement` is Worker 3's abstract form of the
degeneration step of Harris. Its proof is the subject of a separate proof
task. The surjectivity and injectivity inputs are Worker 61's candidates
0ecae5fc and c91ec78b; this module does not depend on them.

For this module Worker 61 read the following passages of Harris 1999:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
  Proposition 4.10, printed p.311 (one-based PDF page 13), read in the
  rendered scan: "Here `Ext^i` denotes the `i`-th derived functor of `Hom`
  in the category of smooth `L_ℓ[GJ]`-modules."
- The same article, §5, printed p.312 (one-based PDF page 14), read in the
  text layer and the rendered scan: "since `π_v` is supercuspidal, the
  higher Ext's vanish and the spectral sequence (4.10.1) degenerates to an
  isomorphism" (5.2).

Interpretation (explanation only). This module supplies only the generic
conditional construction. Harris's statements involve two different
coefficient modules, and the module does not specialize to either of them.

- Proposition 4.10 uses the full coefficient module. In its spectral sequence
  (4.10.1), `C` would be the category of smooth `L_ℓ[GJ]`-modules and the
  coefficient would be the whole module `𝒜_ℓ(GJ, ρ, H)`. `K` would be an
  object whose cohomology is the compactly supported cohomology
  `H_c^{2(n-1)-q}` of the Drinfeld tower `M̆_N`, Tate twisted by `n - 1`.
- The isomorphism (5.2) is stated for selected components, read in the
  rendered scan of printed p.312 (one-based PDF page 14). Its left-hand side
  is `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)]`.
  The coefficient module is restricted to its `π^v`-isotypic part
  `𝒜_ℓ(GJ, ρ, H)[π^v]`, and the `Hom` group is then restricted to its
  `JL(π_v)`-isotypic component. The right-hand side is the `[π]`-component
  `H^j(S̄_K(N), W̃)[π]` of the cohomology of the Shimura variety.

Harris's sentence before (5.2) cites supercuspidality of `π_v` for the
vanishing of "the higher Ext's" in the argument for this restricted
isomorphism. It does not assert that positive Ext groups from the cohomology
of the Drinfeld tower into the whole module `𝒜_ℓ(GJ, ρ, H)` vanish. The
hypothesis `hW` of `smoothDegenerationAddEquiv` requires vanishing of positive
smooth Ext groups from every `H^k K` into the one chosen module `W`. This
module therefore does not claim that `hW` holds for `W = 𝒜_ℓ(GJ, ρ, H)`, nor
that any vanishing comes before the isotypic selections.

Specializing to (5.2) leaves separate obligations, none formalized here:

- choosing the coefficient module and isotypic restrictions for which a
  vanishing hypothesis is actually established;
- passing to the `JL(π_v)`-isotypic component of `Hom` and to the
  `[π]`-component of the target;
- identifying the abutment with the cohomology of the Shimura variety
  compatibly with these restrictions (Proposition 4.10).

## Scope

- `HyperextDegenerationStatement` is a hypothesis of every isomorphism; it is
  not proved here.
- Only additive isomorphisms are constructed; no linearity over a coefficient
  ring, Hecke equivariance or naturality of the isomorphisms is stated. The
  underlying map is the edge map, whose naturality in `K` is `edgeMap_comp`
  of `HyperextAbutmentFiltration`.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance. In the smooth section `R` and `G` share the universe `u`, as
  in `SmoothRep.{u, u, u} R G`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.311 (rendered scan) and p.312 (text layer and rendered scan) read for this
module.

Dependencies: `Langlands.Cohomology.ExtProjectiveResolution`,
`Langlands.Cohomology.HyperextAbutmentFiltration`,
`Langlands.Cohomology.SmoothHyperextSecondPage` and
`Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
