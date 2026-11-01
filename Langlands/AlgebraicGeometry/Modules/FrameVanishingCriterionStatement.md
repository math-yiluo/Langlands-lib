# Vanishing of pulled-back sections in a local frame (statement)

This module states the proposition
`Langlands.SchemeModule.FrameVanishingCriterionStatement`. It supplies a statement target,
not a proof; the proof is the theorem `Langlands.SchemeModule.frameVanishingCriterion` in the
sibling module `Langlands.AlgebraicGeometry.Modules.FrameVanishingCriterionProof`.

## Statement

For every universe `u`, every scheme `X : Scheme.{u}` (with no Noetherian, integrality or
other assumption), every sheaf of modules `M : X.Modules` (not assumed to be a line bundle),
every open `U` of `X`, every section `τ : Γ(M, U)`, every function `a : Γ(X, U)` and every
global section `s : GlobalSections M`:

* **Frame hypothesis.** For every open `W ≤ U`, the map
  `r ↦ r • M.presheaf.map (homOfLE hW).op τ` from functions `Γ(X, W)` on `W` to sections
  `Γ(M, W)` is bijective. In words: `τ` is a frame of `M` on `U`; every section of `M` over
  an open inside `U` is a unique function multiple of the restriction of `τ`.
* **Local expression.** The restriction of `s` from `⊤` to `U` equals `a • τ`; that is,
  `a` is the coefficient of `s` in the frame `τ`.
* **Conclusion.** For every scheme `T : Scheme.{u}` and every morphism `g : T ⟶ X` whose
  preimage of `U` is all of `T` (`hg : ⊤ ≤ g ⁻¹ᵁ U`, so `g` factors through `U`), the
  pullback `pullbackSection g M s` of `s` along `g` is zero if and only if
  `g.appLE U ⊤ hg a = 0`. Here `g.appLE U ⊤ hg a` is the pullback of the function `a` on
  `U` to a global function on `T`.

`pullbackSection` is the published pullback of a global section of a module sheaf along a
morphism (module `Langlands.AlgebraicGeometry.Modules.SectionResidue`), and `GlobalSections`
is the published type of global sections (module
`Langlands.AlgebraicGeometry.Modules.SectionLocus`); both are used unchanged. The published
predicate `VanishesAlong L g s` of `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`
is by definition `pullbackSection g L.obj s = 0`, so for a line bundle `L` the statement
applies directly to it: with `M = L.obj`, it says `VanishesAlong L g s ↔ g.appLE U ⊤ hg a = 0`.

## Mathematics and provenance

The frame hypothesis says that `r ↦ r • τ` is an isomorphism `𝒪_U ≅ M|_U` of module
sheaves on `U`. Pulling back along `g`, which factors through `U`, gives an isomorphism
`g^*M ≅ 𝒪_T` sending `g^*τ` to `1`, and `s|_U = a • τ` gives `g^*s = g^*(a) · g^*τ`.
Hence `g^*s = 0` exactly when the function `g^*(a)` on `T` is zero. This is a standard fact
about trivialized modules. It is stated here as an internal helper, and the derivation just
given is its provenance; no literature statement is transcribed.

## Intended uses

* Local equations of sections of glued line bundles. Cocycle gluing of trivial line bundles
  provides frames on the gluing opens, and the global section glued from local equations
  `a i` has coefficient `a i` in the frame on the `i`-th open. The criterion then reads off
  vanishing of the section along any morphism into that open
  (`Langlands.AlgebraicGeometry.Picard.exists_lineBundle_of_associated_equations`, module
  `Langlands.AlgebraicGeometry.Picard.AssociatedEquationGluing`).
* Through those local equations, the detection of rational points and of tangent vectors
  (`K[ε]`-points) by sections in the proof of the seed-existence statement
  `Langlands.GroupScheme.AlgebraicallyClosedSectionSeedExistenceStatement`
  (proof task ff2d671a-f569-4f74-bab5-c409b9407294).

The Lean text is, unchanged, the required statement text of statement task
75c63d90-3732-4ddc-8eee-8d3c9f495992, which was published from the seed-existence proof task
but never received an executor; it is therefore submitted here together with its proof.
