# Statement: inner forms are detected by the star action

Author: Worker 75.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.InnerFormStarActionStatement.{u}`. The Lean file only defines the
proposition. It contains no proof of it and adds no other declarations or axioms. It
imports [`Rational.InnerDiscrepancy`](../Rational/InnerDiscrepancy.md) (for
`LocalGroupIso.HasInnerDiscrepancy`, and through it `LocalGroupIso`,
`IsAdjointQuotient` and `IsAdjointQuotient.innerAction`),
[`Reductive.StarAction`](StarAction.md) (for `GaloisPinningData`,
`GaloisPinningData.toSplitPinning` and `GaloisPinningData.starAction`) and Mathlib's
`FieldTheory/SeparableClosure` (for `SeparableClosure k`).

## Binders and hypotheses

All objects are in universe `u`. Write `k_s` for `SeparableClosure k` and
`Γ = k_s ≃ₐ[k] k_s` for the absolute Galois group. The proposition quantifies over:

- a field `k : Type u`;
- group schemes `G`, `G'` and `A` over `Spec k`, with `IsAffineHom` and
  `LocallyOfFiniteType` on the structure morphisms of `G` and `G'`;
- a homomorphism `q : G ⟶ A` with `hq : IsAdjointQuotient q`
  ([`Adjoint.Quotient`](../Adjoint/Quotient.md)). This says that `G` is connected
  reductive, `A` is adjoint, `q` is flat, surjective and locally of finite presentation
  with kernel the scheme-theoretic centre of `G`, and `q` has the universal properties of
  the quotient `G/Z_G`. So `A` is `G/Z_G`. `hq.innerAction : AutomorphicAction A G`
  ([`Adjoint.InnerAction`](../Adjoint/InnerAction.md)) is the action of `G/Z_G` on `G`
  induced by conjugation;
- Galois pinning data `d : GaloisPinningData k k_s G` and
  `d' : GaloisPinningData k k_s G'`. Each consists of a torus `T` of the group defined
  over `k` whose base change to `k_s` is a split maximal torus, a reduced root datum of
  `(G_{k_s}, T_{k_s})` on the character and cocharacter lattices of `T_{k_s}`, a base of
  it and a pinning. It includes that the base change to `k_s` is connected reductive.
  `d.toSplitPinning.rootDatum` and `d.toSplitPinning.base` are the root datum and base
  of `d`. `d.starAction σ`, for `σ ∈ Γ`, is the star action
  ([`Reductive.StarAction`](StarAction.md)): the natural action of `σ` on the lattices
  of the `k`-torus followed by the unique Weyl group element that restores the base. It
  is an automorphism of the root datum preserving the base.

## Statement

The proposition is an equivalence between the following two conditions.

1. (*`G'` is an inner form of `G`.*) There are a finite Galois extension `L/k`, with
   `L : Type u` and instances `Field L`, `Algebra k L`, `FiniteDimensional k L` and
   `IsGalois k L`, and
   `e : LocalGroupIso G G' (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))`
   with `e.HasInnerDiscrepancy hq.innerAction`. Here `e` gives, for each scheme `Z` over
   `Spec k` with a map `a : Z ⟶ Spec L`, a group isomorphism `G(Z) ≃* G'(Z)`, natural
   in `Z`; by Yoneda this is an isomorphism `G_L ≅ G'_L` of `L`-groups. The condition
   `HasInnerDiscrepancy` says: for every scheme `T` over `Spec k` and every two maps
   `b c : T ⟶ Spec L` over `k`, there is `x ∈ A(T)` with
   `e_{t ≫ b}(x · g) = e_{t ≫ c}(g)` for every `t : W ⟶ T` and every `g ∈ G(W)`, where
   `x · g` is `hq.innerAction` (pulled back along `t`). So the discrepancy of `e` between
   any two points of `Spec L` is the action of a point of `G/Z_G`.
2. (*The star actions agree.*) There is
   `f : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum`, an
   isomorphism of root data (Mathlib: a weight-lattice isomorphism, a contravariant
   coweight-lattice isomorphism and a bijection of root indices, compatible with roots,
   coroots and the pairing), such that
   - `f` preserves the bases: `a ∈ d.base.support ↔ f.indexEquiv a ∈ d'.base.support`
     for every root index `a`;
   - `f` intertwines the star actions: for every `σ ∈ Γ`,
     `RootPairing.Equiv.comp f (d.starAction σ).val =
      RootPairing.Equiv.comp (d'.starAction σ).val f`.
     (`RootPairing.Equiv.comp g h` is "first `h`, then `g`", so this is
     `f ∘ μ_G(σ) = μ_{G'}(σ) ∘ f`.)

## Source and provenance

The statement is derived from published results; the Lean form is not verbatim. Source:
Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014, registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page = PDF
page.

- Proposition 7.2.2, p.252, for a split connected reductive `k`-group `G₀`: "The fibers
  of H¹(k, Aut_{G₀/k}) → H¹(k, Out_{G₀/k}) are precisely the classes that are inner forms
  of each other."
- Inner forms, p.252: "The image of H¹(k, G/Z_G) in H¹(k, Aut_{G/k}) consists of the
  k-forms of G obtained by twisting by 1-cocycles valued in (G/Z_G)(k_s), which we called
  the inner forms of G."
- Lemma 7.1.1 and its proof, pp.238–239: `k`-forms `G` of `G₀` correspond to
  `H¹(k_s/k, Aut((G₀)_{k_s}))`, through the cocycle `γ ↦ ϕ ∘ γ^*(ϕ)⁻¹` of an isomorphism
  `ϕ : G_K ≅ (G₀)_K` over a finite Galois extension `K/k` (p.239; p.250).
- The `∗`-action, Remark 7.1.2, pp.239–240: `γ ∈ Gal(k_s/k)` acts on the based root
  datum `(R(G), ∆)` through `R(G_{k_s}, T, B) ≃ R(G_{k_s}, γ^*(T), γ^*(B))` followed by
  `G(k_s)`-conjugation back to `(T, B)`; "It is the '∗-action' of Gal(k_s/k) on
  Dyn(Φ)".
- p.256: "If (G₀, T₀, M₀, {X_a}_{a∈∆₀}) denotes the pinned split connected reductive
  k-group with (R(G₀), ∆₀) = (R(G), ∆) then the homomorphism
  Gal(k_s/k) → Aut((R(G), ∆)) = Out_{G₀/k}(k) defines a class in H¹(k, Out_{G₀/k}).
  Using Proposition 7.2.2, the image of this class under the natural section to
  H¹(k, Aut_{G₀/k}) → H¹(k, Out_{G₀/k}) is the quasi-split inner form of G".

The Library's `starAction` is Milne's `∗`-action `σ ∗ α = w_σ(σ α)` (J. S. Milne,
*Algebraic Groups*, 2022, §25.c, printed p.555; documented in
[`Reductive.StarAction`](StarAction.md)), extended to the whole based root datum. It is
the same action as Conrad's: both transport the base by `σ` and return to the original
base by the unique Weyl group element (equivalently, by `G(k_s)`-conjugation, which acts
on root data through the Weyl group).

## Derivation from the source

- *The image of `[G]` in `H¹(k, Out_{G₀/k})`.* Let `G₀` be the pinned split group with
  the based root datum of `G`. Since `G₀` is split, `Out_{G₀/k}` is the constant group of
  `Θ = Aut(R(G₀), ∆₀)` (Theorem 7.1.9(3), p.246). So `Γ` acts trivially on `Θ`, and
  `H¹(k, Out_{G₀/k})` is the set of continuous homomorphisms `Γ → Θ` modulo conjugation
  by `Θ`. By p.256 the section of `H¹(k, Aut_{G₀/k}) → H¹(k, Out_{G₀/k})` sends the class
  of the `∗`-action `μ_G` of `G` to the class of the quasi-split inner form of `G`. That
  form is an inner form of `G`, so by Proposition 7.2.2 it has the same image in
  `H¹(k, Out_{G₀/k})` as `[G]`. The image of a section is sent back to the original
  class. Hence `[G]` maps to the class of `μ_G`, transported to `Θ` by an identification
  `ι : (R(G), ∆) ≅ (R(G₀), ∆₀)`.
- *Translation of Proposition 7.2.2.* Let `G'` be a second form of `G₀`, with
  identification `ι'`. By Proposition 7.2.2, `G'` is an inner form of `G` if and only if
  `[G]` and `[G']` have the same image in `H¹(k, Out_{G₀/k})`, that is, if and only if
  `ι' μ_{G'} ι'⁻¹ = θ (ι μ_G ι⁻¹) θ⁻¹` for some `θ ∈ Θ`. Writing `f = ι'⁻¹ θ ι`, this
  says that the based isomorphism `f : (R(G), ∆) ≅ (R(G'), ∆')` intertwines `μ_G` and
  `μ_{G'}`. Every based isomorphism `f` arises from `θ = ι' f ι⁻¹`. This is condition 2.
- *Groups that are not forms of a common `G₀`.* If the based root data of `d` and `d'`
  are not isomorphic, both conditions fail: condition 1 gives `G_L ≅ G'_L`, hence
  isomorphic based root data over `k_s`. So the proposition need not assume that `G` and
  `G'` are forms of each other.
- *Inner forms.* Condition 1 is the encoding of "`G'` is an inner form of `G`" used by
  the Library's [`Rational.QuasiSplitInnerForm`](../Rational/QuasiSplitInnerForm.md) and
  [`Reductive.SemilocalQuasiSplitInnerFormStatement`](SemilocalQuasiSplitInnerFormStatement.md).
  A twist of `G` by a continuous cocycle valued in `(G/Z_G)(k_s)` is inflated from some
  finite Galois `L/k` and comes with `ϕ : G_L ≅ G'_L` whose discrepancies
  `ϕ⁻¹ ∘ γ^*(ϕ)`, `γ ∈ Gal(L/k)`, are actions of points of `A(L)`. For a scheme `T` and
  two maps `b c : T ⟶ Spec L`, the pair `(b, c)` factors through
  `Spec (L ⊗_k L) = ∐_{γ ∈ Gal(L/k)} Spec L`, so the discrepancy over `T` is glued from
  these. Conversely, condition 1 at `T = Spec L`, `b = 𝟙`, `c = Spec γ` gives an
  `A(L)`-valued cocycle twisting `G` into `G'`.
- *Conventions for the star action.* Conrad's `γ^*` and Milne's `σ` may differ by
  `σ ↦ σ⁻¹`. Condition 2 quantifies over all `σ ∈ Γ` and uses the same construction on
  both sides, so it does not depend on this choice.
- *Choices.* The proposition holds for every choice of Galois pinning data `d`, `d'`. For
  another choice the star actions change by based isomorphisms that intertwine them
  (Library [`Reductive.StarActionStatement`](StarActionStatement.md),
  `StarActionIndependenceStatement`), so condition 2 does not depend on the choice.
- *Adjoint quotient.* Conrad's `G/Z_G` acting on `G` is `A` with `hq.innerAction`. The
  quotient is unique up to unique isomorphism by its universal property.

## Scope and not stated

- Fields only. The relative version over a base scheme (Conrad p.253, Exercise 7.3.8) is
  not stated.
- The statement does not mention `H¹`. It does not state the bijection
  `H¹(k, Out_{G₀/k}) ≅ Hom(Γ, Θ)/Θ`, the surjectivity of
  `H¹(k, Aut_{G/k}) → H¹(k, Out_{G/k})` (p.252), or that being an inner form is an
  equivalence relation.
- It does not assert the existence of `A`, `q`, `d` or `d'`. Without them it holds
  vacuously. (The Library proves that a smooth affine `k`-group has a maximal `k`-torus,
  and that tori split over a finite Galois extension; existence of full Galois pinning
  data is a separate statement, as noted in [`Reductive.StarAction`](StarAction.md).)
- It does not state continuity of the star action
  ([`Reductive.StarActionStatement`](StarActionStatement.md),
  `StarActionContinuityStatement`); condition 2 is over all of `Γ`.

## Role in the Library

This is a statement for the program of algebraic and reductive group schemes with
rational and Galois structure. A separate proof task will prove it. A possible route:
for (1 ⇒ 2), extend `e` to `k_s`, move the torus and base of `d` along it, conjugate back
to those of `d'` by a point of `G'(k_s)` (conjugacy of pairs of a maximal torus and a
Borel subgroup over `k_s`), and use that the discrepancies are inner, so they act on
based root data trivially. For (2 ⇒ 1), use the Isomorphism Theorem over `k_s` to get a
pinned isomorphism `G_{k_s} ≅ G'_{k_s}` inducing `f`, descend it to a finite Galois
extension, and show that its discrepancies have trivial image in the based root datum
automorphisms, hence are inner (Conrad Proposition 7.1.6, p.243). This module proves no
relation to other statements.
