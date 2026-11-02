# Cohomology retraction from a trace along an affine morphism

This module turns a "trace" morphism into a retraction of cohomology. It is the
final formal step towards `FiniteFlatCohomologyRetractStatement`. The
construction of the trace for a finite flat morphism of constant rank `d` is not
part of this module; the trace enters only as a hypothesis.

Throughout, `K` is a field in universe `u`, `f^*` and `f_*` are Mathlib's module
pullback and pushforward `Scheme.Modules.pullback` and `Scheme.Modules.pushforward`,
and `η : M ⟶ f_* f^* M` is the unit of their adjunction
`Scheme.Modules.pullbackPushforwardAdjunction`. For `g : Y ⟶ Spec K`, the `K`-module
`Hⁿ(Y, M)` is the Library's `DerivedSections.relativeCohomology g n`, the `n`-th right
derived functor of `M ↦ Γ(Y, M)` viewed as a `K`-module through `g`.

## Additivity of cohomology

The instance `DerivedSections.relativeCohomology_additive g n` states that
`relativeCohomology g n` is an additive functor, for any `g : X ⟶ Spec R` with
`R : CommRingCat.{u}`. It is the Library instance
`CechResolution.rightDerived_additive` (right derived functors of additive functors
are additive) applied to the additive functor `relativeGlobalSections g`.

When `R` is `CommRingCat.of K` for a field `K`, Lean's instance search does not find
this instance by itself, so the proofs below supply it by hand. The reason is that the
search builds the preadditive structure on `ModuleCat K` from the field structure of
`K`, which differs syntactically from the general `CommRingCat` one.

## Retract from a scaled section

`retractOfCompEqNsmul i r d hd h`: let `A B : ModuleCat K` and `i : A ⟶ B`,
`r : B ⟶ A` with `i ≫ r = d • 𝟙 A` for a natural number `d` with `(d : K) ≠ 0`. Then
`A` is a retract of `B`, with section `i` and retraction `(d : K)⁻¹ • r`. Indeed
`i ≫ ((d : K)⁻¹ • r) = (d : K)⁻¹ • (d • 𝟙 A) = 𝟙 A`.

## The retraction for an affine morphism

`cohomologyRetractOfTrace h g M d hd t ht n` takes:

- an affine morphism of schemes `h : X ⟶ Y` (`IsAffineHom h`) and `g : Y ⟶ Spec K`,
- a quasi-coherent `M : Y.Modules`,
- a natural number `d` with `(d : K) ≠ 0`,
- a morphism `t : h_* h^* M ⟶ M` with `η ≫ t = d • 𝟙 M` (hypothesis `ht`),
- a degree `n`.

It returns a `Retract` of `K`-modules: `Hⁿ(Y, M)` (computed through `g`) is a retract
of `Hⁿ(X, h^* M)` (computed through `h ≫ g`).

The construction works as follows. `h^* M` is quasi-coherent by the Library instance
`Langlands.Scheme.Modules.isQuasicoherent_pullback`. Then the Library's
`DerivedSections.affinePushforwardCohomologyIso h g (h^* M) n` gives an isomorphism
`e : Hⁿ(X, h^* M) ≅ Hⁿ(Y, h_* h^* M)`. That isomorphism uses the vanishing of higher
direct images of quasi-coherent modules under affine morphisms. Write `Hⁿ` for
`relativeCohomology g n`. The section is `Hⁿ(η) ≫ e⁻¹`, and before scaling the
retraction is `e ≫ Hⁿ(t)`. Their composite is

`Hⁿ(η) ≫ e⁻¹ ≫ e ≫ Hⁿ(t) = Hⁿ(η ≫ t) = Hⁿ(d • 𝟙 M) = d • 𝟙`,

where the last step uses additivity of `Hⁿ` (`Functor.map_nsmul`). Then
`retractOfCompEqNsmul` rescales the retraction by `(d : K)⁻¹`.

## The statement over `Spec K`

`finiteFlatCohomologyRetract_of_trace f M d hd t ht n` is the same result for a
morphism `f : X ⟶ Y` in `Over (Spec K)` with `IsAffineHom f.left`. It concludes

`Nonempty (Retract ((relativeCohomology Y.hom n).obj M)
  ((relativeCohomology X.hom n).obj (f.left^* M)))`,

which is the conclusion of `FiniteFlatCohomologyRetractStatement`. The proof rewrites
`X.hom` as `f.left ≫ Y.hom` (Mathlib's `Over.w f`) and applies
`cohomologyRetractOfTrace f.left Y.hom`.

To prove the full statement from this one, two things remain. First, a finite morphism
is affine, which Mathlib provides as an instance. Second, a finite flat morphism of
constant rank `d` that is locally of finite presentation needs a morphism
`t : f_* f^* M ⟶ M` with `η ≫ t = d • 𝟙 M`. That trace is built separately and is not
claimed here.

## Provenance and scope

This is an internal helper. It formalizes the formal half of the splitting step in
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd edition (1994), proof of
Proposition 6.13 (i), printed p. 124. The source is cited in the statement's Markdown
`FiniteFlatCohomologyRetractStatement.md`. There, the composite `L → ψ_* ψ^* L → L` of
the unit and the trace is multiplication by the degree. So once the degree is
inverted, the cohomology of `L` is a direct summand of the cohomology of `ψ_* ψ^* L`,
which equals the cohomology of `ψ^* L` because `ψ` is affine. The Lean route goes through the published Library results named above and
pinned Mathlib (`Mathlib/CategoryTheory/Retract.lean`,
`Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean`,
`Mathlib/CategoryTheory/Comma/Over/Basic.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`). Nothing is asserted about the existence
of a trace, about finiteness or flatness, or about the retraction being natural in
`M`.
