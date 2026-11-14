# Statement: forms of a split reductive group over a finite field

Author: Worker 75.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.FiniteFieldFormClassificationStatement.{u}`. The Lean file only
defines the proposition. It contains no proof of it and adds no other declarations or
axioms. It imports [`Reductive.StarAction`](StarAction.md) (for `GaloisPinningData`,
`GaloisPinningData.toSplitPinning` and `GaloisPinningData.starAction`, and through it
`SplitPinning` from [`Reductive.Pinning`](Pinning.md) and `SplitPinning.basedRootDatumAut`
from [`Reductive.PinnedAutomorphismLift`](PinnedAutomorphismLift.md)), Mathlib's
`FieldTheory/Finite/Basic` (for `FiniteField.frobeniusAlgEquivOfAlgebraic`) and Mathlib's
`FieldTheory/SeparableClosure` (for `SeparableClosure k`).

## Binders and hypotheses

All objects are in universe `u`. Write `k_s` for `SeparableClosure k`. The proposition
quantifies over:

- a finite field `k : Type u`, with instances `Field k` and `Fintype k`;
- a group scheme `G₀` over `Spec k` with `IsAffineHom` on its structure morphism;
- a split pinning `p : SplitPinning G₀` ([`Reductive.Pinning`](Pinning.md)). It says that
  `G₀` is connected reductive and consists of a split maximal torus `T₀` of `G₀` over `k`,
  a reduced root datum `R = p.rootDatum` of `(G₀, T₀)` on the character and cocharacter
  lattices of `T₀` with finite index type, a base `Δ = p.base` and simple-root Lie
  vectors. So `(G₀, T₀)` is a split connected reductive `k`-group with a pinning.

Write `Θ = p.basedRootDatumAut`
([`Reductive.PinnedAutomorphismLift`](PinnedAutomorphismLift.md)). It is the subgroup of
`RootPairing.Aut p.rootDatum` of automorphisms `e` of the root datum with
`a ∈ Δ ↔ e.indexEquiv a ∈ Δ` for every root index `a`, that is, `Θ = Aut(R, Δ)`.

Write `Frob = FiniteField.frobeniusAlgEquivOfAlgebraic k k_s : k_s ≃ₐ[k] k_s`. It is the
arithmetic Frobenius `x ↦ x^q` with `q = #k` (Mathlib, `coe_frobeniusAlgEquivOfAlgebraic`).

## The class of a group

The statement uses a local predicate `HasClass G d θ`, for a group scheme `G` over `Spec k`
with `IsAffineHom` and `LocallyOfFiniteType` on its structure morphism, Galois pinning
data `d : GaloisPinningData k k_s G` ([`Reductive.StarAction`](StarAction.md)) and
`θ ∈ Θ`. The data `d` consist of a torus of `G` defined over `k` whose base change to `k_s`
is a split maximal torus, a reduced root datum of `(G_{k_s}, T_{k_s})`, a base of it and
a pinning. They include that `G_{k_s}` is connected reductive. `d.starAction σ`, for
`σ ∈ Gal(k_s/k)`, is the star action: the natural action of `σ` on the lattices of the
`k`-torus followed by the unique Weyl group element that restores the base. It is an
element of the group of based automorphisms of the root datum of `d`. The predicate is:

`HasClass G d θ`: there is
`f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum`, an isomorphism of root
data (Mathlib: a weight-lattice isomorphism, a contravariant coweight-lattice isomorphism
and a bijection of root indices, compatible with roots, coroots and the pairing), with

- `a ∈ p.base.support ↔ f.indexEquiv a ∈ d.toSplitPinning.base.support` for every root
  index `a` (so `f` carries `Δ` onto the base of `d`), and
- `RootPairing.Equiv.comp f θ.val =
   RootPairing.Equiv.comp (d.starAction Frob).val f`.
  (`RootPairing.Equiv.comp g h` is "first `h`, then `g`", so this is
  `f ∘ θ = μ_d(Frob) ∘ f`, where `μ_d = d.starAction`.)

So `HasClass G d θ` says that `G` is a form of `G₀` (its based root datum over `k_s` is
isomorphic to `(R, Δ)`) and that, transported to `Θ` by `f`, the star action of Frobenius
on `G` is `θ`.

## Statement

The proposition is the conjunction of two clauses.

1. (*Existence.*) For every `θ ∈ Θ` with `IsOfFinOrder θ`, there are a group scheme `G`
   over `Spec k` with instances `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`
   and Galois pinning data `d : GaloisPinningData k k_s G` with `HasClass G d θ`.
2. (*Classification.*) For all group schemes `G` and `G'` over `Spec k`, each with
   `IsAffineHom` and `LocallyOfFiniteType` on its structure morphism, all Galois pinning
   data `d` of `G` and `d'` of `G'` over `k_s`, and all `θ θ' ∈ Θ`: if `HasClass G d θ`
   and `HasClass G' d' θ'`, then `Nonempty (G ≅ G') ↔ IsConj θ θ'`. Here `G ≅ G'` is an
   isomorphism of group schemes over `Spec k`, and `IsConj θ θ'` is conjugacy in the
   group `Θ`.

Every `G` with Galois pinning data `d` whose based root datum is isomorphic to `(R, Δ)`
by some `f` has the class `θ = f⁻¹ ∘ μ_d(Frob) ∘ f`. By clause 2 with `G' = G` the class
of `G` is well defined up to conjugacy and does not depend on `d`. Together the clauses
say that `G ↦ (class of G)` is a bijection from isomorphism classes of such `k`-groups to
conjugacy classes of finite-order elements of `Θ`.

## Source and provenance

The statement is derived from published results; the Lean form is not verbatim. Source:
Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014, registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page = PDF
page.

- Example 7.2.3, p.252: "Let k be a finite field, and let (G₀, T₀, M) be a split
  connected reductive k-group. Let R be the root datum and ∆ a base of the associated
  root system, so Θ := Aut(R, ∆) is identified with the constant component group
  Out_{G₀/k} of Aut_{G₀/k}. The natural surjective map H¹(k, Aut_{G₀/k}) → H¹(k, Θ_k) is
  bijective because the fiber through each class [G] is an image of the set
  H¹(k, G/Z_G) that consists of a single point. Since Θ_k is a constant group and
  Gal(k_s/k) = Ẑ with generator given by Frob_k, the cohomology set H¹(k, Θ_k) consists
  of conjugacy classes of elements θ ∈ Θ = Aut(R, ∆). Hence, the isomorphism classes of
  k-forms of G₀ are classified by the conjugacy classes in Θ = Aut(R, ∆)."
- The same example continues: to each `θ ∈ Θ` it associates "the k-form G_θ of G₀
  obtained by replacing the Frob_k-action on G₀(k_s) with the usual action followed by
  the action of θ on G₀ via the pinning", using Theorem 6.1.17 to identify `Θ` with the
  automorphisms of the pinned group.
- p.252, before the example: "If k is finite then H¹(k, G/Z_G) is a single point, due to
  Lang's Theorem [Bo91, 16.5(i)]." Proposition 7.2.2, p.252: "The fibers of
  H¹(k, Aut_{G₀/k}) → H¹(k, Out_{G₀/k}) are precisely the classes that are inner forms of
  each other."
- p.256: the class in `H¹(k, Out_{G₀/k})` of a `k`-form `G` is given by the homomorphism
  `Gal(k_s/k) → Aut((R(G), ∆)) = Out_{G₀/k}(k)` of the `∗`-action. The `∗`-action is
  Remark 7.1.2, pp.239–240: `γ` acts on `(R(G), ∆)` through
  `R(G_{k_s}, T, B) ≃ R(G_{k_s}, γ^*(T), γ^*(B))` followed by `G(k_s)`-conjugation back
  to `(T, B)`.

The Library's `starAction` is Milne's `∗`-action `σ ∗ α = w_σ(σ α)` (J. S. Milne,
*Algebraic Groups*, 2022, §25.c, printed p.555; documented in
[`Reductive.StarAction`](StarAction.md)), extended to the whole based root datum. It
transports the base by `σ` and returns to it by the unique Weyl group element, which is
the effect of Conrad's `G(k_s)`-conjugation on root data.

## Derivation from the source

- *Cohomology of the constant group `Θ_k`.* `Gal(k_s/k)` is profinite and acts trivially
  on `Θ`, so `H¹(k, Θ_k)` is the set of continuous homomorphisms `Gal(k_s/k) → Θ`
  (with `Θ` discrete) modulo conjugation by `Θ`. Such a homomorphism is determined by the
  image `θ` of the topological generator `Frob`. Its image is finite, so `θ` has finite
  order; conversely each finite-order `θ` gives the continuous homomorphism
  `Ẑ → Θ, 1 ↦ θ`. So `H¹(k, Θ_k)` is the set of conjugacy classes of finite-order elements
  of `Θ`. Conrad writes "conjugacy classes of elements θ ∈ Θ". If `R` is semisimple
  then `Θ` is finite and every element has finite order. In general `Θ` can be infinite:
  for `G₀ = 𝔾_m²`, `Θ = GL₂(ℤ)`. Elements of infinite order are not classes of forms,
  because `μ_d(Frob)` has finite order (the torus of `d` splits over a finite Galois
  extension, through whose Galois group `μ_d` factors). This is why clause 1 assumes
  `IsOfFinOrder θ`.
- *The class of a form.* By p.256, the image of `[G] ∈ H¹(k, Aut_{G₀/k})` in
  `H¹(k, Θ_k)` is the class of the `∗`-action of `G`, transported to `Θ` by an
  identification of based root data. This is the homomorphism `σ ↦ f⁻¹ ∘ μ_d(σ) ∘ f`,
  determined by its value `f⁻¹ ∘ μ_d(Frob) ∘ f` at `Frob`. So "`[G]` maps to the class
  of `θ`" is `HasClass G d θ` (up to replacing `θ` by a conjugate, that is, changing
  `f`).
- *Clause 2* is the injectivity of `H¹(k, Aut_{G₀/k}) → H¹(k, Θ_k)` together with the
  description of `H¹(k, Θ_k)`: two forms are isomorphic if and only if their classes in
  `H¹(k, Aut_{G₀/k})` agree, if and only if the Frobenius values of their `∗`-actions
  are conjugate in `Θ`. Isomorphism classes of `k`-forms of `G₀` correspond to
  `H¹(k, Aut_{G₀/k})` (Lemma 7.1.1, pp.238–239).
- *Clause 1* is the surjectivity: each finite-order `θ` is the class of a form, namely of
  Conrad's `G_θ`. The statement asserts that such a form exists; it does not fix the
  construction.
- *Conventions.* Conrad's `γ^*` and Milne's `σ` may differ by `σ ↦ σ⁻¹`, and one could use
  the geometric Frobenius `Frob⁻¹`. Either change replaces every class `θ` by `θ⁻¹`.
  Inversion preserves finite order and conjugacy, and `θ ↦ θ⁻¹` is a bijection of `Θ`, so
  both clauses are unaffected.
- *Choices.* For different Galois pinning data of the same group the star actions differ
  by a based isomorphism that intertwines them (Library
  [`Reductive.StarActionStatement`](StarActionStatement.md),
  `StarActionIndependenceStatement`), which changes the class by conjugation in `Θ`.
  Clause 2 does not depend on these choices.
- *Hypotheses on `G`.* `IsAffineHom` and `LocallyOfFiniteType` are the instance arguments
  of `GaloisPinningData` and `GaloisPinningData.starAction`. A `k`-form of `G₀` has them,
  so clause 1 asserts them for the form it produces.

## Scope and not stated

- Only finite fields are treated. Remark 7.2.4 (p.253: the same classification over a
  henselian local ring with finite residue field) is not stated.
- The statement does not mention `H¹`. It does not state that `H¹(k, G/Z_G)` is a single
  point (Lang's theorem; compare the Library's
  [`FiniteFieldTorsorPointStatement`](../FiniteFieldTorsorPointStatement.md)) or the
  bijectivity of `H¹(k, Aut_{G₀/k}) → H¹(k, Θ_k)` as such.
- It does not state the construction of `G_θ` by twisting the Frobenius action through the
  pinning, or that `G_θ` is quasi-split (every connected reductive group over a finite
  field is quasi-split: [`Rational.FiniteFieldQuasiSplitStatement`](../Rational/FiniteFieldQuasiSplitStatement.md)).
- It does not state the consequences drawn in Example 7.2.3 (p.252–253): forms of a simply
  connected or adjoint semisimple `G₀` correspond to conjugacy classes in
  `Aut(Dyn(Φ))`; a connected semisimple `k`-group with irreducible root system is split
  when `Dyn(Φ)` has no nontrivial automorphisms (types `A₁`, `B`, `C`, `E₇`, `E₈`, `F₄`,
  `G₂`); the counts of forms in types `A_n`, `E₆`, `D_n` and `D₄`.
- Clause 1 does not assert that `G` is the base change of anything or name a splitting
  field.

## Role in the Library

This is a statement for the program of algebraic and reductive group schemes with
rational and Galois structure. A separate proof task will prove it. A possible route:
for clause 2 (⇐), conjugacy of `θ` and `θ'` gives a based isomorphism of the root data of
`d` and `d'` intertwining the Frobenius star actions, hence all star actions (they factor
through a finite Galois group generated by `Frob`; Library
`StarActionContinuityStatement`); by Conrad Proposition 7.2.2 `G'` is then an inner form of
`G`, and Lang's theorem for the connected group `G/Z_G` makes the inner twist trivial.
For (⇒), transport `d` along an isomorphism `G ≅ G'` and compare with `d'` by
`StarActionIndependenceStatement`. For clause 1, twist the Frobenius action on `G₀(k_s)`
by the pinned automorphism of `G₀` lifting `θ` (`SplitPinning.basedRootDatumAutLift`)
and descend along a finite extension `k'/k` of degree a multiple of the order of `θ`.
This module proves no relation to other statements.
