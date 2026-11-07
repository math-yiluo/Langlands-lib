# Smoothness of scheme morphisms from lifting along Artinian thickenings

This module gives a scheme form of the infinitesimal lifting criterion over a
locally noetherian base. Lifting is required only along thickenings of spectra
of local Artinian rings. The source is The Stacks Project, More on Morphisms,
Lemma 37.12.1 (Tag 02HX), implication (4) ⇒ (1), in the snapshot
`stacks-artin-axioms-approximation-2026-11-06`, file `02HX.html`.

Namespace: `Langlands.AlgebraicGeometry.ArtinianLiftingSmooth`. All schemes and
rings live in one universe `u`.

## The lifting condition

For a morphism of schemes `g : Y ⟶ Z`, `LiftsArtinian g : Prop` says the
following. Let `B'` and `B` be local Artinian rings in `Type u` and
`φ : B' →+* B` a surjection with `maximalIdeal B' * ker φ = ⊥`. Let
`α : Spec B ⟶ Y` and `β : Spec B' ⟶ Z` satisfy `α ≫ g = Spec φ ≫ β`. Assume the
residue point `Spec (ResidueField B) ⟶ Spec B ⟶ Y` (the spectrum of the residue
map, followed by `α`) is locally of finite type. Then some
`γ : Spec B' ⟶ Y` has `γ ≫ g = β` and `Spec φ ≫ γ = α`.

Compared with Stacks (4) there are two differences:

- The kernel need only be annihilated by the maximal ideal of `B'`. Small
  extensions also have length-one kernels, so more surjections are tested. This
  is the convention of the Library's `ArtinianTest.IsElementarySurjection`.
- Stacks fixes a point `x` and asks that `α` send the closed point to `x` with
  `κ(x) ≅ κ(m)`. Here no point is fixed. The residue point must instead be
  locally of finite type. For a closed point of an affine open with that
  residue field, the residue point is a closed immersion followed by an open
  immersion, so it qualifies. Points with larger residue fields are also
  tested.

## Main result

`smooth_of_liftsArtinian (g : Y ⟶ Z) [IsLocallyNoetherian Z]
[LocallyOfFiniteType g] (h : LiftsArtinian g) : Smooth g`.

Proof. By `HasRingHomProperty.iff_appLE` it suffices to show that for affine
opens `U` of `Z` and `V` of `Y` with `V ≤ g⁻¹ U`, the ring map
`g.appLE U V e : Γ(Z, U) → Γ(Y, V)` is smooth. `Γ(Z, U)` is noetherian, and the
ring map is of finite type because `g` is locally of finite type. The
ring-level theorem `Langlands.RingTheory.ArtinianLifting.smooth` reduces this to
`HasArtinianLifting Γ(Z, U) Γ(Y, V)`.

So let `φ : B' → B` and `ψ : Γ(Y, V) → B` be as in that condition. Put
`α = Spec ψ ≫ hV.fromSpec` and `β = Spec (algebraMap Γ(Z, U) B') ≫
hU.fromSpec`. Then:

- `α ≫ g = Spec φ ≫ β`, by `IsAffineOpen.SpecMap_appLE_fromSpec` and because
  `ψ` and `φ` are algebra maps.
- The residue point of `α` is `Spec` of the surjection `S → ResidueField B`,
  a closed immersion (`IsClosedImmersion.spec_of_surjective`), followed by the
  open immersion `hV.fromSpec`. So it is locally of finite type.

The hypothesis gives `γ`. `Spec B'` has one point, since `B'` is local Artinian.
That point is the image of the closed point of `Spec B`. Since
`Spec φ ≫ γ = α`, its image under `γ` is the image of the closed point under
`α`, which lies in `V`. Hence `γ` factors through the open
immersion `hV.fromSpec` (`IsOpenImmersion.lift`), as `Spec ψ''` for a ring map
`ψ'' : Γ(Y, V) → B'` (`Spec.preimage`). Cancelling the monomorphisms
`hU.fromSpec` and `hV.fromSpec`, and using `Spec.map_injective`, shows that
`ψ''` is a `Γ(Z, U)`-algebra map and that `φ ∘ ψ'' = ψ`.

## Provenance

Derived from The Stacks Project, More on Morphisms, Lemma 37.12.1 (Tag 02HX),
implication (4) ⇒ (1). The source proof restricts to affine opens and applies
Algebra, Lemma 10.141.2. The Lean proof also restricts to affine opens, and uses
the ring-level criterion of `Langlands.RingTheory.Smooth.ArtinianLifting`. The
hypothesis is the variant described above, and the conclusion is smoothness of
the whole morphism rather than smoothness at one point.
