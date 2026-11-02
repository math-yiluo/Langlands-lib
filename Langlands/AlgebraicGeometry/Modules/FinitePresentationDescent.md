# Descent of local finite presentation along fppf coverings

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent`.
All declarations are in the namespace `Langlands.AlgebraicGeometry.Modules`.

## Main result

`isFinitePresentation_of_pullback_fppf`: let `p : X ⟶ Y` be a morphism of
schemes that is flat, locally of finite presentation and surjective. Let
`M : Y.Modules` be a sheaf of modules whose pullback
`(Scheme.Modules.pullback p).obj M` is locally finitely presented (Mathlib's
`IsFinitePresentation`). Then `M` is locally finitely presented.

No quasi-coherence hypothesis is placed on `M`. Mathlib defines
`IsFinitePresentation` through local presentations (`QuasicoherentData`), so
the conclusion includes quasi-coherence of `M`.

## Purpose and provenance

Workers 311 and 214 requested this lemma for the proof task `5b9ad399`, which
proves algebraicity of the coherent stack. It serves the representability of
the Picard sheaf in task `d084a453`. The lemma resembles the classical fpqc
descent of finite presentation for quasi-coherent modules. The statement here
differs from it: `M` is an arbitrary sheaf of modules, and the covering is a
single flat, locally finitely presented surjection. The statement and the proof
below were written for this development. The proof works with stalks and with
the openness of the locus where a morphism is a stalk isomorphism. No
literature theorem is cited.

## Proof outline

Fix `y : Y`.

1. The stalk of `M` at `y` is finitely presented over the local ring
   (`finitePresentation_stalk_of_pullback`). Choose a point `x` over `y`. The
   stalk of the pullback at `x` is the base change of the stalk of `M` along the
   local ring map at `x`, and that local ring map is faithfully flat.
   Commutative-algebra descent then applies.
2. Choose generators `b : Fin n → stalk M y` with surjection `π` from `Oⁿ`, and
   relation vectors `κ : Fin m → Fin n → O` that span the kernel of `π`. Here
   `O` is the local ring at `y`. Lift `b` and `κ` to sections over a common open
   neighbourhood `V` of `y`. The lifted relations `∑ k, r j k • s k` have zero
   germ, so they vanish on a smaller open `W`.
3. Take an affine chart `h : Spec A ⟶ Y` inside `W` through `y = h a₀`. The
   restricted sections give global sections `s'` of the restriction of `M` along
   `h`. The restricted functions give relation vectors `ρ` with coefficients in
   `A`, and the relations `∑ k, ρ j k • s' k = 0` hold. Let `N` be the finitely
   presented `A`-module `Aⁿ / span ρ`. The map `presentedMap` from `N` to global
   sections sends the generators to `s'`. Let `c` be its associated morphism
   `tilde N ⟶ M.restrict h`.
4. `c` is bijective on stalks at `a₀` (`mem_isoLocus_chart`). The stalk map is
   compared with the stalk of `M` at `y` through the Library linear
   equivalence `restrictStalkLinearEquiv`. The lemma
   `Langlands.CommutativeAlgebra.bijective_of_presentation` applies because
   the chart identifies the local ring at `a₀` with `O`.
5. The iso locus of `c` is open (`isOpen_isoLocus_of_pullback`). Both
   `tilde N` and `M.restrict h` become locally finitely presented after pullback
   along the base change `pullback.snd p h`. For `M.restrict h`, this pullback is
   isomorphic to the pullback of the pullback of `M` along `p`.
6. On the open iso locus `W'`, the restriction of `c` is an isomorphism. The
   finite presentation of `tilde N` therefore transports to a finite
   presentation of the restriction of `M` to the image of `W'` in `Y`, which
   contains `y`.

Finally, finite presentations on an open neighbourhood of every point assemble
into Mathlib's `QuasicoherentData` with finite presentations.

## Declarations

### Assembly

- `isFinitePresentation_of_forall_exists_presentation`: if every point of `Y`
  has an open neighbourhood `U` on which the restriction of `M` has a finite
  presentation, then `M.IsFinitePresentation`. The opens indexed by the points
  of `Y` cover `Y`. The presentations become `presentationOverOfRestrict`
  (Library `FinitePresentationPullback`), which forms the quasi-coherent data.
- `exists_presentation_opensRange`: a finite presentation of the restriction of
  `M` along an open immersion `g` gives one of the restriction to the open image
  `g.opensRange`.
- `isFinitePresentation_of_presentation`: a global finite presentation makes a
  module sheaf locally finitely presented.
- `exists_presentation_tilde`: for a finitely presented `A`-module `N`, the
  sheaf `tilde N` has a finite presentation. This uses Mathlib's
  `presentationTilde`, with finite generating sets of `N` and of the relation
  kernel.

### Lifting germs

- `mem_iInf_of_finite`: a point of each of finitely many opens lies in their
  infimum.
- `exists_forall_germ_eq` and `exists_forall_germ_eq_ring`: finitely many
  elements of a module stalk, or of the local ring, are germs of sections over
  one common open neighbourhood.
- `exists_le_forall_map_eq_zero`: finitely many sections over `V` with zero
  germ at `y` all restrict to zero on one open `W ≤ V` containing `y`.

### The affine chart

In this section `h : Spec A ⟶ Y` is an open immersion.

- `restrict_smul_Spec`: for a function `r` on the image `h ''ᵁ ⊤`, acting by
  the coordinate-ring element corresponding to `r` on a global section of the
  restriction of `M` is the same as acting by `r` on that section of `M`.
- `stalkMap_germ_appIso_inv'`: the local ring map of `h` at `x` sends the germ
  at `h x` of the function corresponding to `r : Γ(Spec A, ⊤)` to the germ of
  `r` at `x`.
- `germ_smul_toStalk`: on a stalk of `tilde N`, the germ of the function
  corresponding to `a : A` acts on the localization of `z` as the localization
  of `a • z`.
- `sum_smul_single`: a vector `v : Fin n → R` is `∑ k, v k • Pi.single k 1`.
- An instance: for `ρ : Fin m → Fin n → R`, the quotient
  `(Fin n → R) ⧸ span (range ρ)` is finitely presented.
- `presentedMap F s ρ hρs`: for `F : (Spec A).Modules`, global sections
  `s : Fin n → moduleSpecΓFunctor.obj F` and relation vectors `ρ` with
  `∑ k, ρ j k • s k = 0` for every `j`, this is the `A`-linear map from
  `(Fin n → A) ⧸ span (range ρ)` that sends the class of `Pi.single k 1` to
  `s k`. That value is the lemma `presentedMap_single`.
- `span_range_toStalk_eq_top`: the localizations at `a₀` of a spanning family of
  an `A`-module `N` span the stalk of `tilde N` at `a₀` over the local ring.
- `mem_isoLocus_chart`: let `s` and `ρ` be as for `presentedMap`, with
  `F = M.restrict h`, and let `κ` be relation vectors over the local ring of `Y`
  at `h a₀`. Suppose the local ring map of `h` sends each `κ j k` to the germ
  of `ρ j k`. Suppose the germs at `h a₀` of the `s k` span the stalk of `M`
  there, and every relation among these germs lies in the span of the `κ j`.
  Then `a₀` lies in the iso locus of
  `tilde.map (presentedMap (M.restrict h) s ρ hρs) ≫ (M.restrict h).fromTildeΓ`.

### Descent

- `finitePresentation_stalk_of_pullback`: let `p` be flat and surjective, and
  let the pullback of `M` along `p` be locally finitely presented. Then every
  stalk of `M` is finitely presented over the local ring. The proof uses the
  Library lemmas `finitePresentation_stalk`,
  `StalkPullback.pullbackStalkTensorEquiv` and `faithfullyFlat_stalkMap`, and
  `Langlands.CommutativeAlgebra.finitePresentation_of_finitePresentation_tensorProduct`.
- `exists_presentation_restrict_of_pullback`: let `p` be flat, locally of finite
  presentation and surjective, and let the pullback of `M` along `p` be locally
  finitely presented. Then every point `y` has an open neighbourhood `U` on
  which the restriction of `M` has a finite presentation. The proof is steps
  1–6 of the outline.
- `isFinitePresentation_of_pullback_fppf`: the main result. It combines the
  previous lemma with `isFinitePresentation_of_forall_exists_presentation`.
