# Faithfully flat descent for coalgebras and for groupoid-like ring data

Authors: Worker 239, Worker 1224.

This helper module, namespace
`Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent`, proves effective descent for
modules along a faithfully flat ring map, in the form of coalgebras for the comonad of
extension and restriction of scalars. It then applies this to ring data shaped like an affine
étale equivalence relation that maps cartesianly to one with an affine quotient. It
introduces no axioms. Its main mathematical input is Mathlib's comonadicity theorem
`comonadicExtendScalars` (`Mathlib/Algebra/Category/ModuleCat/Descent.lean`, pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`): for a faithfully flat ring map
`f : A →+* B`, extension of scalars `ModuleCat A ⥤ ModuleCat B` is comonadic. The rest of the
module uses standard Mathlib API for adjunctions, tensor products and `Algebra.IsPushout`.

## Source

- `stacks-descent-modules-2026-11-01` (directory SHA-256
  `216c92cc547dc34f00f0eaa7354703aced00a51f02c908d58a3758395f4dfe4f`):
  `023F.html` (Section 35.3, Descent for modules), `023G.html` (Definition 35.3.1, descent
  data `(N, φ)` for modules relative to `R → A`), `023J.html` (Definition 35.3.4, effective
  descent data), `023M.html` (Lemma 35.3.6, exactness of the Amitsur complex for faithfully
  flat `R → A`) and `023N.html` (Proposition 35.3.9: for faithfully flat `R → A` every
  descent datum on modules is effective, `M ↦ (A ⊗_R M, can)` is an equivalence, and its
  inverse is `(N, φ) ↦ H^0(s(N_•))`, the module of invariant elements).
- `stacks-noetherian-approximation-2026-11-01` (directory SHA-256
  `a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`): `0245.html`
  (Lemma 35.37.1, effective descent of affine morphisms along fpqc coverings). Its proof, for a
  single faithfully flat ring map `R → A`, is the source of Part 3 (see there).

A coalgebra `(N, a : N → A ⊗_R N)` for the comonad `N ↦ A ⊗_R N` is a form of descent datum.
Its structure map `a` determines an `A ⊗_R A`-linear map `N ⊗_R A → A ⊗_R N` as in
Definition 35.3.1. This correspondence is standard but is neither formalized nor used here;
the module works with coalgebras only. The "coinvariants" below play the role of the
invariant elements `H^0` in Proposition 35.3.9 (3). `isIso_descentMap` is the coalgebra form
of the effectivity in Proposition 35.3.9 (1). The Lean proof does not follow Stacks' proof
(base change to a ring map with a section). It derives the result from Mathlib's
comonadicity theorem, a Beck-type argument.

## Part 1: general adjunctions (section `General`)

For an adjunction `adj : L ⊣ R` between arbitrary categories:

- `homEquiv_comp_eq`: if `f : comparison B ⟶ X` is a map of coalgebras for
  `adj.toComonad` (with `Comonad.comparison`), then its transpose
  `adj.homEquiv _ _ f.f : B ⟶ R X.A` equalizes `R.map X.a` and the unit
  `adj.unit.app (R.obj X.A)`.
- `comparison_a_comp_eq`: conversely, if `ι : E ⟶ R X.A` equalizes these two maps, then for
  every `g : B ⟶ E` the transpose `(adj.homEquiv _ _).symm (g ≫ ι)` satisfies the coalgebra
  map condition out of `comparison B`.

Both are short computations with naturality of the unit and counit and a triangle identity.
They are internal lemmas: standard adjunction calculus, not taken from a source.

## Part 2: coalgebras over a ring map (section `Coalgebra`)

Fix commutative rings `A₀ B₀ : Type u` and `φ : A₀ →+* B₀`.

- `descentComonad φ`: the comonad `(extendRestrictScalarsAdj φ).toComonad` on
  `ModuleCat B₀`. Its underlying functor sends `N` to `B₀ ⊗[A₀] N`, viewed as a `B₀`-module
  through the left factor.
- `coinvariants φ X`: for a coalgebra `X`, the `A₀`-submodule of `X.A`, with `A₀` acting
  through `φ`, of the elements `n` with `X.a n = 1 ⊗ n`. It is
  `LinearMap.eqLocus` of the coaction and of the unit `n ↦ 1 ⊗ n`. `coinvariantsι` is its
  inclusion and `coinvariantsι_comp` records the equalizing property.
- `descentMap φ X : B₀ ⊗[A₀] coinvariants φ X ⟶ X.A`: the adjoint transpose of the
  inclusion, `b ⊗ n ↦ b • n`.
- `coinvariantsHomEquiv φ B X`: coalgebra maps `comparison B ⟶ X` correspond bijectively to
  `A₀`-linear maps `B ⟶ coinvariants φ X` (by Part 1). It is natural in `B`.
  `coinvariantsFunctor φ` is the resulting functor and `coinvariantsAdjunction φ` is the
  adjunction `Comonad.comparison (extendRestrictScalarsAdj φ) ⊣ coinvariantsFunctor φ`
  (Mathlib's `Adjunction.rightAdjointOfEquiv` and `Adjunction.adjunctionOfEquivRight`).
  `coinvariantsAdjunction_counit_f` says that the counit at `X` has underlying map
  `descentMap φ X`.
- `isIso_descentMap φ hφ X` (**faithfully flat descent for coalgebras**): if
  `φ.FaithfullyFlat`, then `descentMap φ X` is an isomorphism for every coalgebra `X`.
  Proof: `(comonadicExtendScalars hφ).eqv` makes the comparison functor an equivalence, so it
  is fully faithful and `X` is isomorphic to `comparison M` for some `M`. Mathlib's
  `Adjunction.isIso_counit_app_of_iso` then makes the counit of `coinvariantsAdjunction` an
  isomorphism at `X`. Its underlying map is `descentMap φ X`.
- `bijective_descentMap`: the same statement for the underlying function.

## Part 3: groupoid-like ring data (section `GroupoidDescent`)

`isPushout_eqLocus_of_groupoid`. Let `A₀ B₀ B C C₂ : Type u` be commutative rings, with
ring maps `φ : A₀ →+* B₀` (faithfully flat), `F : B₀ →+* B`, `τ σ : B →+* C`, `d : C →+* B`
and `ι₁ ι₂ c : C →+* C₂`. Assume:

- `hP`: the square `A₀ → B₀` (`φ`), `A₀ → B` (`F ∘ φ`), `B₀ → C` (`τ ∘ F`), `B → C` (`σ`) is
  a pushout in `CommRingCat`, so `C = B₀ ⊗[A₀] B`;
- `hP₂`: the square `B → C` (`σ`), `B → C` (`τ`), `C → C₂` (`ι₁`), `C → C₂` (`ι₂`) is a
  pushout, so `C₂ = C ⊗[σ, B, τ] C`;
- `d ∘ τ = d ∘ σ = id_B` (a unit), and `c ∘ τ = ι₁ ∘ τ`, `c ∘ σ = ι₂ ∘ σ` (a composition);
- `hmem`: `F (φ a)` lies in the equalizer `τ.eqLocus σ` for every `a`.

Then, with `A = τ.eqLocus σ` (the subring `{b | τ b = σ b}`), the square `A₀ → B₀` (`φ`),
`A₀ → A` (`F ∘ φ` corestricted), `B₀ → B` (`F`), `A → B` (inclusion) is a pushout in
`CommRingCat`. So `B ≅ B₀ ⊗[A₀] A`.

Proof. With the algebra structures given by `RingHom.toAlgebra`,
`Algebra.IsPushout.equiv` gives `e : B₀ ⊗[A₀] B ≃ₐ[B₀] C`, `e (b₀ ⊗ b) = τ (F b₀) * σ b`. The
coaction is `a = e⁻¹ ∘ τ : B →ₐ[B₀] B₀ ⊗[A₀] B`. With these instances, the carrier of
`descentComonad φ` at `B` is definitionally `B₀ ⊗[A₀] B`, and its double application is
definitionally `B₀ ⊗[A₀] (B₀ ⊗[A₀] B)`. So `a` is a coalgebra structure map once the axioms
hold:

- counit: the counit of the comonad equals `d ∘ e` on `B₀ ⊗[A₀] B` (check on pure tensors),
  so it sends `a b` to `d (τ b) = b`;
- coassociativity: pasting `hP` and `hP₂` gives a pushout identifying
  `C₂ = B₀ ⊗[A₀] C`. Composing with `id ⊗ e` gives an `A₀`-algebra isomorphism
  `Ψ : B₀ ⊗[A₀] (B₀ ⊗[A₀] B) ≃ C₂` with `Ψ (b₀ ⊗ y) = ι₁ (τ (F b₀)) * ι₂ (e y)`. On pure
  tensors, `Ψ ∘ δ = c ∘ e` and `Ψ ∘ (G a) = ι₁ ∘ e`, using `ι₁ ∘ σ = ι₂ ∘ τ`. Here `δ` is the
  comultiplication of the comonad and `G a` its value on `a`. Hence both sides of
  coassociativity, applied to `a b` and mapped by `Ψ`, equal `c (τ b) = ι₁ (τ b)`, and `Ψ` is
  injective.

The coinvariants of this coalgebra are exactly `A`, since `a n = 1 ⊗ n` if and only if
`τ n = e (1 ⊗ n) = σ n`. By `bijective_descentMap`, `b₀ ⊗ x ↦ b₀ • x` is a bijection
`B₀ ⊗[A₀] A → B`. This is `Algebra.IsPushout A₀ B₀ A B` (`IsBaseChange.of_equiv`), and
`CommRingCat.isPushout_of_isPushout` turns it into the stated pushout square.

Provenance. The theorem is derived from the proof of Stacks Lemma 35.37.1 (Tag 0245,
`0245.html`) for a single faithfully flat ring map `R → A` (here `A₀ → B₀`). There, an affine
`V = Spec B` over `Spec A` with a descent datum gives a descent datum for modules on `B`.
Proposition 35.3.9 gives `C = Ker(B → A ⊗_R B)` with `A ⊗_R C ≅ B`, and `C` is a subring
because the descent datum is a ring map. In the Lean theorem the descent datum is the
coaction `a = e⁻¹ ∘ τ`, built from the groupoid data (`τ`, `σ`, unit `d`, composition `c`)
instead of an isomorphism over `A ⊗_R A`. The invariants are the equalizer `τ.eqLocus σ`,
which is a subring by construction. The hypotheses on `d` and `c` are the internal form of the
counit and coassociativity axioms; they are not stated in this form in the source.

## Role

This module is the algebraic core of the proof of
`EtaleEquivalenceRelationCartesianAffineQuotientStatement`. That proof is in
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientProof`.
