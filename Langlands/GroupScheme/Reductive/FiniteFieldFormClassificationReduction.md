# Forms over a finite field: reduction to inner forms and to the existence clause

Author: Worker 148.

Lean module: `Langlands.GroupScheme.Reductive.FiniteFieldFormClassificationReduction`.

This module defines one `Prop`-valued statement,
`Langlands.GroupScheme.FiniteFieldFormClassificationReductionStatement.{u}`, and proves it
(`finiteFieldFormClassificationReduction`). The statement is the implication

`InnerFormStarActionStatement.{u} → FiniteFieldFormExistenceStatement.{u} →
FiniteFieldFormClassificationStatement.{u}`.

- `FiniteFieldFormClassificationStatement`
  ([`Reductive.FiniteFieldFormClassificationStatement`](FiniteFieldFormClassificationStatement.md))
  is the classification of forms of a split connected reductive group `G₀` over a finite
  field `k` (Conrad, *Reductive group schemes*, Example 7.2.3). Clause 1: every finite-order
  `θ ∈ Θ = Aut(R, Δ)` is the class of some `G` with Galois pinning data `d`. Clause 2: if
  `G` with `d` has class `θ` and `G'` with `d'` has class `θ'`, then `G ≅ G'` over `k` if
  and only if `θ` and `θ'` are conjugate in `Θ`. Here "`G` with `d` has class `θ`" means:
  some base-preserving root-datum isomorphism `f` from the root datum of the pinning `p` of
  `G₀` to that of `d` satisfies `f ∘ θ = μ_d(Frob) ∘ f`, where `μ_d = d.starAction` and
  `Frob` is the arithmetic Frobenius of `k_s = SeparableClosure k`.
- `FiniteFieldFormExistenceStatement`
  ([`Reductive.FiniteFieldFormExistenceStatement`](FiniteFieldFormExistenceStatement.md))
  is clause 1 of the classification statement, stated on its own.
- `InnerFormStarActionStatement`
  ([`Reductive.InnerFormStarActionStatement`](InnerFormStarActionStatement.md)) says, for an
  arbitrary field `k`, groups `G`, `G'` with Galois pinning data `d`, `d'` over `k_s` and an
  adjoint quotient `q : G ⟶ A` of `G`: some finite Galois extension `L/k` carries a local
  isomorphism `e` from `G` to `G'` over `Spec L` whose discrepancy is inner
  (`e.HasInnerDiscrepancy hq.innerAction`, Conrad Proposition 7.2.2) if and only if some
  base-preserving root-datum isomorphism `F` from `d` to `d'` intertwines `d.starAction σ`
  and `d'.starAction σ` for every `σ ∈ Gal(k_s/k)`.

So clause 2 of the classification is proved here in full from `InnerFormStarActionStatement`,
and clause 1 is taken from `FiniteFieldFormExistenceStatement`. Neither premise is proved in
this module, and the module does not prove `FiniteFieldFormClassificationStatement` itself.

## Declarations

Namespace `Langlands.GroupScheme.FiniteFieldFormClassification`, root-pairing algebra. Here
`RootPairing.Equiv.comp g h` is "first `h`, then `g`", `RootPairing.Equiv.symm P Q f` is the
inverse of `f : RootPairing.Equiv P Q`, and the root pairings are over any commutative ring.

- `symm_comp_self f`: `f⁻¹ ∘ f = id`.
- `self_comp_symm f`: `f ∘ f⁻¹ = id`.
- `symm_comp_of_comp_eq h`: if `f ∘ θ = μ ∘ f` (`θ`, `μ` automorphisms), then
  `f⁻¹ ∘ μ = θ ∘ f⁻¹`.
- `comp_intertwine_of_conj hθ hθ' hc`: if `f ∘ θ = μ ∘ f`, `f' ∘ θ' = μ' ∘ f'` and
  `c ∘ θ = θ' ∘ c`, then `F = f' ∘ c ∘ f⁻¹` satisfies `F ∘ μ = μ' ∘ F`.
- `conj_of_comp_intertwine hθ hθ' hF`: if `f ∘ θ = μ ∘ f`, `f' ∘ θ' = μ' ∘ f'` and
  `F ∘ μ = μ' ∘ F`, then `c = f'⁻¹ ∘ F ∘ f` satisfies `c ∘ θ = θ' ∘ c`.
- `comp_pow_of_comp_eq h n`: if `F ∘ x = y ∘ F` then `F ∘ xⁿ = yⁿ ∘ F` for every `n : ℕ`.

Same namespace, finite fields (`k` a finite field, `k_s = SeparableClosure k`,
`Frob = FiniteField.frobeniusAlgEquivOfAlgebraic k k_s`):

- `exists_frobenius_pow_eq L σ`: for an intermediate field `L` of `k_s/k` that is finite
  dimensional over `k` and any `σ ∈ Gal(k_s/k)`, there is `n : ℕ` with `σ x = Frobⁿ x` for
  all `x ∈ L`.
- `exists_starAction_eq_pow d d' σ`: for Galois pinning data `d`, `d'` over `k_s` of two
  groups `G`, `G'` over `k` (affine, locally of finite type) and any `σ ∈ Gal(k_s/k)`,
  there is one `n : ℕ` with `d.starAction σ = (d.starAction Frob)ⁿ` and
  `d'.starAction σ = (d'.starAction Frob)ⁿ`.

Namespace `Langlands.GroupScheme`:

- `finiteFieldFormClassification_of_innerFormStarAction hinner hexist`: from
  `hinner : InnerFormStarActionStatement.{u}` and
  `hexist : FiniteFieldFormExistenceStatement.{u}`, a proof of
  `FiniteFieldFormClassificationStatement.{u}`.
- `FiniteFieldFormClassificationReductionStatement.{u} : Prop`, the implication displayed
  above.
- `finiteFieldFormClassificationReduction : FiniteFieldFormClassificationReductionStatement.{u}`,
  which applies the previous theorem.

## Proofs

*Root-pairing algebra.* `symm_comp_self` and `self_comp_symm` are checked componentwise
(weight map, coweight map, index bijection) with Mathlib's
`RootPairing.Equiv.weightEquiv_symm_weightMap`, `weightMap_weightEquiv_symm`,
`coweightMap_coweightEquiv_symm` and `coweightEquiv_symm_coweightMap`. The other three
algebraic lemmas are rewriting with `RootPairing.Equiv.comp_assoc`, `id_comp`, `comp_id`
and the two inverse laws. `comp_pow_of_comp_eq` is induction on `n`, using that the power
in `RootPairing.Aut` is `x^(n+1) = x^n ∘ x` and `x^0 = id`.

*Frobenius powers.* For `exists_frobenius_pow_eq`, `L` is finite, so the restriction
`σ.restrictNormal L ∈ Gal(L/k)` is a power `Frob_Lⁿ` of the Frobenius of `L` (Mathlib,
`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`). Both `Frob_Lⁿ` and `Frobⁿ` act as
`x ↦ x^(qⁿ)` (`coe_frobeniusAlgEquivOfAlgebraic_iterate`), and
`AlgEquiv.restrictNormal_commutes` identifies `σ x` with the restriction for `x ∈ L`.
For `exists_starAction_eq_pow`, the Library theorem `starActionContinuity` gives finite
subextensions `L₁`, `L₂` such that every `τ` fixing `L₁` (resp. `L₂`) pointwise has trivial
star action for `d` (resp. `d'`). Apply `exists_frobenius_pow_eq` to `L₁ ⊔ L₂` (finite by
`IntermediateField.finiteDimensional_sup`) to get `n`, put `φ = Frobⁿ`, and write
`σ = φ · (φ⁻¹σ)`. Then `φ⁻¹σ` fixes `L₁ ⊔ L₂`, so its star actions are `1`. Since
`starAction` is a group homomorphism, `μ_d(σ) = μ_d(Frob)ⁿ`, and likewise for `d'`.

*Main theorem.* Fix `k`, `G₀`, `p`. Clause 1 is `hexist` applied to `k`, `G₀`, `p`. For
clause 2 take `G`, `G'`, `d`, `d'`, `θ`, `θ'` and unpack the two class hypotheses into
`f, hf, hθ` (`f ∘ θ = μ_d(Frob) ∘ f`) and `f', hf', hθ'`. `G` is connected reductive by the
Library theorem `connectedReductiveAlgebraicExtensionReflection` applied to `k_s/k` and
`d.isConnectedReductive`, so `adjointQuotientExistence` gives `q : G ⟶ A` with
`hq : IsAdjointQuotient q`.

- (⇒) Let `φ : G ≅ G'`. Over `L = k`, `LocalGroupIso.ofIso φ _` is a local isomorphism with
  inner discrepancy (`LocalGroupIso.ofIso_hasInnerDiscrepancy`), and `k/k` is finite
  Galois. The forward direction of `hinner k G G' A q hq d d'` gives a base-preserving
  `F` with `F ∘ μ_d(σ) = μ_{d'}(σ) ∘ F` for all `σ`, in particular for `σ = Frob`. By
  `conj_of_comp_intertwine`, `c = f'⁻¹ ∘ F ∘ f` satisfies `c ∘ θ = θ' ∘ c`. It preserves
  `Δ` (from `hf`, the base condition on `F` and `hf'`), so `c ∈ Θ`, and `c θ c⁻¹ = θ'`
  (`mul_inv_eq_iff_eq_mul`), which is `IsConj θ θ'` (`isConj_iff`).
- (⇐) Let `c ∈ Θ` with `c θ c⁻¹ = θ'`, so `c ∘ θ = θ' ∘ c`. Put `F = f' ∘ c ∘ f⁻¹`. It
  carries the base of `d` onto the base of `d'` (from `hf`, `c ∈ Θ` and `hf'`), and by
  `comp_intertwine_of_conj` it intertwines `μ_d(Frob)` and `μ_{d'}(Frob)`. For any `σ`,
  `exists_starAction_eq_pow` gives one `n` with `μ_d(σ) = μ_d(Frob)ⁿ` and
  `μ_{d'}(σ) = μ_{d'}(Frob)ⁿ`, and `comp_pow_of_comp_eq` shows that `F` intertwines these.
  The reverse direction of `hinner k G G' A q hq d d'` then gives a finite Galois extension
  `L/k` and a local isomorphism `e` from `G` to `G'` over `Spec L` with inner discrepancy
  `he`. The Library's `LocalGroupIso.innerCocycle` builds from `he` (and the faithfulness
  `hq.innerAction_isFaithful` of the inner action) a cocycle of `A` on `Spec L` with
  discrepancy equation `innerCocycle_hasDiscrepancy`. `A` is adjoint, hence semisimple and
  connected reductive, hence smooth, affine and connected, so the cocycle is trivial by
  Lang's theorem in the Library form `Cocycle.isTrivial_of_finite`. The cover
  `Spec L → Spec k` is surjective, flat and quasi-compact (`fieldExtension_fpqc`), and
  `LocalGroupIso.descendOfTrivial` turns `e` with a trivial discrepancy cocycle into an
  isomorphism `G ≅ G'` over `k`.

The proof uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
through the Library and Mathlib.

## Source and provenance

The new statement `FiniteFieldFormClassificationReductionStatement` is internal: it is an
implication between three Library statements, two of them published
(`FiniteFieldFormClassificationStatement`, `InnerFormStarActionStatement`) and one new in
this contribution (`FiniteFieldFormExistenceStatement`), and it is proved here. The proof
of clause 2 follows Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, p.252: Proposition 7.2.2 (the fibres of
`H¹(k, Aut_{G₀/k}) → H¹(k, Out_{G₀/k})` are the inner forms; here in the form
`InnerFormStarActionStatement`), Lang's theorem ("If k is finite then H¹(k, G/Z_G) is a
single point"; here `Cocycle.isTrivial_of_finite` for `A = G/Z_G`) and Example 7.2.3 (a
class in `H¹(k, Θ_k)` is determined by the value at the generator `Frob` of
`Gal(k_s/k) = Ẑ`; here `exists_starAction_eq_pow`, which uses that the star action
factors through a finite quotient of `Gal(k_s/k)` in which `Frob` generates).

## Scope

- `InnerFormStarActionStatement` is used in both directions. It is stated for arbitrary
  fields; only its finite-field instances are used.
- Clause 1 is not proved here; it is the premise `FiniteFieldFormExistenceStatement`.
- `FiniteFieldFormClassificationStatement` follows as soon as both premises are proved, by
  applying `finiteFieldFormClassificationReduction` (or
  `finiteFieldFormClassification_of_innerFormStarAction`) to their proofs.
