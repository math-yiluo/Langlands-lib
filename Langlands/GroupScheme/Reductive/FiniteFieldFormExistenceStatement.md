# Statement: every finite-order based automorphism is the class of a form over a finite field

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.FiniteFieldFormExistenceStatement.{u}`. The Lean file only defines
the proposition. It contains no proof of it and adds no other declarations or axioms. It has
the same imports as [`Reductive.FiniteFieldFormClassificationStatement`](FiniteFieldFormClassificationStatement.md):
[`Reductive.StarAction`](StarAction.md) (for `GaloisPinningData`,
`GaloisPinningData.toSplitPinning` and `GaloisPinningData.starAction`, and through it
`SplitPinning` and `SplitPinning.basedRootDatumAut`), Mathlib's `FieldTheory/Finite/Basic`
(for `FiniteField.frobeniusAlgEquivOfAlgebraic`) and Mathlib's `FieldTheory/SeparableClosure`
(for `SeparableClosure k`).

## Relation to the classification statement

The proposition is, word for word, clause 1 (*existence*) of the Library statement
`FiniteFieldFormClassificationStatement`
([`Reductive.FiniteFieldFormClassificationStatement`](FiniteFieldFormClassificationStatement.md)).
The only difference is that the local predicate `HasClass G d θ` of that statement is
written out. The binders, hypotheses and conventions are the same, so the explanations in
that statement's Markdown apply unchanged. It is stated on its own so that it can be proved
separately. The module
[`Reductive.FiniteFieldFormClassificationReduction`](FiniteFieldFormClassificationReduction.md)
proves that it and `InnerFormStarActionStatement` together imply
`FiniteFieldFormClassificationStatement`.

## Binders and hypotheses

All objects are in universe `u`. Write `k_s` for `SeparableClosure k`. The proposition
quantifies over:

- a finite field `k : Type u`, with instances `Field k` and `Fintype k`;
- a group scheme `G₀` over `Spec k` with `IsAffineHom` on its structure morphism;
- a split pinning `p : SplitPinning G₀` ([`Reductive.Pinning`](Pinning.md)). It says that
  `G₀` is connected reductive. It consists of a split maximal torus `T₀` of `G₀` over `k`,
  a reduced root datum `R = p.rootDatum` of `(G₀, T₀)` with finite index type, a base
  `Δ = p.base` and simple-root Lie vectors;
- `θ : p.basedRootDatumAut`, an element of `Θ = Aut(R, Δ)`, the subgroup of
  `RootPairing.Aut p.rootDatum` of automorphisms `e` with `a ∈ Δ ↔ e.indexEquiv a ∈ Δ` for
  every root index `a` ([`Reductive.PinnedAutomorphismLift`](PinnedAutomorphismLift.md));
- the hypothesis `IsOfFinOrder θ`: `θ` has finite order in the group `Θ`.

Write `Frob = FiniteField.frobeniusAlgEquivOfAlgebraic k k_s : k_s ≃ₐ[k] k_s`, the
arithmetic Frobenius `x ↦ x^q` with `q = #k`.

## Statement

There exist

- a group scheme `G` over `Spec k`, with `IsAffineHom G.X.hom` and
  `LocallyOfFiniteType G.X.hom`;
- Galois pinning data `d : GaloisPinningData k k_s G` ([`Reductive.StarAction`](StarAction.md)):
  a torus of `G` defined over `k` whose base change to `k_s` is a split maximal torus, a
  reduced root datum of `(G_{k_s}, T_{k_s})`, a base of it and a pinning; the data include
  that `G_{k_s}` is connected reductive;
- an isomorphism of root data
  `f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum`,

such that

- `a ∈ p.base.support ↔ f.indexEquiv a ∈ d.toSplitPinning.base.support` for every root
  index `a` (`f` carries `Δ` onto the base of `d`), and
- `RootPairing.Equiv.comp f θ.val = RootPairing.Equiv.comp (d.starAction Frob).val f`,
  that is, `f ∘ θ = μ_d(Frob) ∘ f` with `μ_d = d.starAction` the star action.

In the terms of the classification statement: `G` is a `k`-form of `G₀` with class `θ`.

## Source and provenance

The statement is derived from a published result; the Lean form is not verbatim. Source:
Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014, registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page = PDF
page.

- Example 7.2.3, p.252: "The natural surjective map H¹(k, Aut_{G₀/k}) → H¹(k, Θ_k) is
  bijective […] Since Θ_k is a constant group and Gal(k_s/k) = Ẑ with generator given by
  Frob_k, the cohomology set H¹(k, Θ_k) consists of conjugacy classes of elements
  θ ∈ Θ = Aut(R, ∆). […] to each θ ∈ Θ we associate the k-form G_θ of G₀ obtained by
  replacing the Frob_k-action on G₀(k_s) with the usual action followed by the action of
  θ on G₀ via the pinning."
- p.252, before the example: "The commutativity of (7.2.2) also gives that
  H¹(k, Aut_{G/k}) → H¹(k, Out_{G/k}) is surjective, since the analogous surjectivity holds
  for G₀ (due to a k-group section to Aut_{G₀/k} → Out_{G₀/k} defined by a choice of
  pinning)."

The present statement is the surjectivity part: every class in `H¹(k, Θ_k)` comes from a
`k`-form. The translation of "class of a form" into `d.starAction Frob`, the restriction to
`θ` of finite order (an element of `H¹(k, Θ_k)` is a continuous homomorphism `Ẑ → Θ`, so
its value at `Frob` has finite order) and the convention remarks (arithmetic versus
geometric Frobenius changes `θ` into `θ⁻¹`, which preserves finite order) are explained in
the section "Derivation from the source" (items *Cohomology of the constant group `Θ_k`*,
*The class of a form*, *Clause 1* and *Conventions*) of the Markdown of
[`Reductive.FiniteFieldFormClassificationStatement`](FiniteFieldFormClassificationStatement.md),
and apply verbatim here.

## Scope and not stated

- The statement does not fix the construction of `G`; Conrad's `G_θ` is one possible
  witness. It does not assert that `G` is quasi-split, that `G` splits over a given finite
  extension, or that `G` is unique (uniqueness up to isomorphism is clause 2 of the
  classification statement).
- Only finite fields are treated.

## Role in the Library

This is an intermediate statement for the proof of `FiniteFieldFormClassificationStatement`.
A possible route: twist the Frobenius action on `G₀` over a finite extension
`k'/k` of degree a multiple of the order of `θ` by the pinned automorphism lifting `θ`
(`SplitPinning.basedRootDatumAutLift`), descend with the Library's pinned Galois descent
(`Reductive.PinnedGaloisDatum`, `Reductive.PinnedGaloisBorel`), and compute the star action
of the descended `k`-torus. This module proves no relation to other statements.
