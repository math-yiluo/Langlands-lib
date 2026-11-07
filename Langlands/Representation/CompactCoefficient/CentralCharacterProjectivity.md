# Projectivity and injectivity with a fixed central character

Author: Worker 1709. Module
`Langlands.Representation.CompactCoefficient.CentralCharacterProjectivity`,
namespace `Langlands.CentralCharacterProjectivity`.

Generic form of Renard VI.3.6, the Proposition after the Lemma (printed p.148 /
PDF p.154, source `renard-2026-representations-groupes-reductifs-padiques`):
an irreducible representation with central character `χ` whose restriction to
an open normal subgroup `H` is compact, with `H Z(G)` of finite index, is
projective and injective in `M(G)_χ`. Renard applies this with `H = ⁰G`. The
categorical packaging is derived; Renard's proof is described in the target
statement's Markdown, and the route here is described below.

## The subcategory `M(G)_χ`

For a group `G` with a topology and `χ : Subgroup.center G →* ℂˣ`:

- `hom_ext'`: morphisms of `SmoothRep.{0, uG, uV} ℂ G` with the same underlying
  map are equal.
- `centralCharacterProperty χ` (an `abbrev`) is the object property
  `fun A => A.HasCentralCharacter χ` on `SmoothRep.{0, uG, uV} ℂ G`. This is
  literally the property `C` of the target statement. Renard fixes a smooth
  `χ`; here, as in the target, `χ` is an arbitrary homomorphism. For a
  topological group `G`, the published `SmoothRep.HasCentralCharacter.isLocallyConstant`
  shows that a nonzero object forces `χ` to be locally constant, so for a
  non-smooth `χ` only zero representations have the property. This is not used
  in the proofs.
- Instances: it contains a zero object (every vector of a zero object is `0`),
  is closed under subobjects (a monomorphism is injective, and `z` acts by `χ z`
  on the image) and under quotients (an epimorphism is surjective). With
  Mathlib's `CategoryTheory.Abelian.Subcategory`, the inclusion functor
  preserves epimorphisms and monomorphisms.
- `surjective_of_epi`, `injective_of_mono`: an epimorphism (monomorphism) of the
  full subcategory has surjective (injective) underlying intertwiner.
- `centralDefect χ A z : A ⟶ A` is `A z - χ z • id`. It is a morphism because
  `z` is central (`centralDefect_apply` gives its value), and it is natural:
  `comp_centralDefect` says `f ≫ centralDefect χ B z = centralDefect χ A z ≫ f`.
  `centralDefect_eq_zero` and `hasCentralCharacter_of_centralDefect` show that
  `A.HasCentralCharacter χ` holds exactly when all central defects vanish.
- `hasCentralCharacter_pushout`: the pushout, in smooth representations, of
  two morphisms out of `X` into objects `Y`, `Z` with central character `χ` has
  central character `χ`. Its central defect vanishes after composing with both
  pushout injections (naturality, and the defects of `Y` and `Z` vanish), so it
  is zero by `pushout.hom_ext`.

## Main theorem

`projective_and_injective_of_compactRestriction H χ τ hχ hirr hc` assumes
`[NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]`,
`H : OpenSubgroup G` with `[H.toSubgroup.Normal]` and
`[(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]`,
`τ : SmoothRep.{0, uG, uV} ℂ G`, `hχ : τ.HasCentralCharacter χ`,
`hirr : τ.IsIrreducible`, and
`hc : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup H.toSubgroup τ).representation`.
It concludes

`Projective (C := (centralCharacterProperty χ).FullSubcategory) ⟨τ, hχ⟩ ∧
Injective (C := (centralCharacterProperty χ).FullSubcategory) ⟨τ, hχ⟩`.

Let `N := H.toSubgroup ⊔ center G`; `G ⧸ N` is finite.

- **Projective.** Given `f : ⟨τ⟩ ⟶ X` and an epimorphism `e : E ⟶ X` of the
  subcategory, `e` is surjective. `RestrictedSplitting.exists_restricted_lift`
  gives an `H`-equivariant linear `l₀ : τ → E` with `e ∘ l₀ = f`. Both `τ` and
  `E` have central character `χ`, so `l₀` is `N`-equivariant
  (`isEquivariantOn_sup_center`). Its average over `G ⧸ N` (`averageMap`) is an
  intertwiner, and `e ∘ average l₀ = average (e ∘ l₀) = average f = f`
  (`average_comp_left`, `average_intertwiningMap`).
- **Injective.** Given `g : X ⟶ ⟨τ⟩` and a monomorphism `f : X ⟶ Y` of the
  subcategory, `f` is injective, hence a monomorphism of smooth
  representations. Form the pushout `P` of `f` and `g` in the abelian category
  of smooth representations. It has central character `χ`, and
  `pushout.inr : τ ⟶ P` is a monomorphism (`Abelian.mono_pushout_of_mono_f`),
  hence injective. `RestrictedSplitting.exists_restricted_retraction` gives an
  `H`-equivariant retraction `r₀`, again `N`-equivariant; its average `r` is a
  `G`-equivariant retraction of `pushout.inr` (`average_comp_right`,
  `average_intertwiningMap`). The extension is `pushout.inl ≫ r`:
  `f ≫ pushout.inl ≫ r = g ≫ pushout.inr ≫ r = g` by `pushout.condition`.

Unlike Renard's proof, no reduction to the block of `τ` and no semisimplicity of
the other representation is used: the lifting and retraction lemmas on `H` need
only smoothness of the other representations.
