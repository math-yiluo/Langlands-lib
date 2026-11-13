# The group `T` of an irreducible representation (Renard VI.4.4, proof)

Worker 114. This module proves the published proposition
`Langlands.CuspidalSupport.RationalTwistStabilizerKernelStatement`
as the theorem `Langlands.CuspidalSupport.rationalTwistStabilizerKernel`,
with the statement's universes `uF` and `uV`. It adds no hypothesis. The statement's
Lean/Markdown pair and everything it imports stay unchanged.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, registered as
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The source is VI.4.4,
the paragraph defining `T` and the Remark after it (printed pp.156–157 / PDF pp.162–163), as
cited by the task and the statement. The Lean proof follows the route in the task context. It
uses the published finiteness lemma V.2.7 (`rationalTwistStabilizerFinite`) and does not
follow the book's wording line by line.

## Notation

Fix `F`, a connected reductive `G` and an irreducible smooth complex representation `A` of
`G(F)`. Write `ν` for the norm characters `χ ↦ |χ|`, `⁰G = commonNormKernel ν`
(= `rationalCommonNormKernel G`), and `X = unramifiedCharacters ν`. In the statement,
`T = ⨅ (ω : X) (_ : Nonempty (A ⊗ ω ≅ A)), ker ω`.

## Auxiliary declarations (all in namespace `TwistStabilizerKernel`)

These are internal helpers of this proof and have no separate literature counterpart.

### Duality (`section Duality`)

- `complex_hasEnoughRootsOfUnity_exponent`: `ℂ` has enough roots of unity for the exponent of
  any finite group. It holds because `ℂ` is algebraically closed and the exponent is a nonzero
  natural number.
- `exists_eq_of_forall_eq_one` (double annihilator): let `S` be a finite commutative group,
  `emb : S →* (Γ →* ℂˣ)` and `ω : Γ →* ℂˣ`. If `ω g = 1` whenever `emb s g = 1` for all `s`,
  then `ω = emb s` for some `s`. Proof: let `ev : Γ →* (S →* ℂˣ)` be `g ↦ (s ↦ emb s g)`. The
  hypothesis says `ker ev ≤ ker ω`, so `ω` descends to a character `ψ` of the subgroup
  `ev.range` of the finite dual `S →* ℂˣ`. Mathlib's `MonoidHom.domRestrict_surjective`
  extends `ψ` to the whole dual. `CommGroup.monoidHomMonoidHomEquiv`, the canonical
  isomorphism of `S` with its double dual, turns this extension into an element `s` of `S`.
  `CommGroup.apply_monoidHomMonoidHomEquiv` then gives `emb s g = ψ (ev g) = ω g`.

### Characters and polynomial functions (`section Generic`)

This section works for any topological group `G` and family of norm characters `ν`.

- `quotientEvaluation : G ⧸ ⁰G →* (X → ℂ)` sends a class `[g]` to the evaluation
  `χ ↦ χ(g)`, through `unramifiedCharacterDescend`. `quotientEvaluation_mk` identifies it with
  the published `unramifiedEvaluation ν g`. `quotientEvaluationHom q : X →* ℂ` is the same
  evaluation, viewed as a character of the group `X`.
- `exists_unramifiedCharacter_apply_ne_one` (separation): if `⁰G` is open and `g ∉ ⁰G`, some
  `ν i` has `ν i g ≠ 1`. Then `ν i` coerced to `ℂˣ` is trivial on `⁰G`. Openness of `⁰G` makes
  it continuous at `1`, hence continuous. So it is an element of `X`, and its value at `g` is
  not `1`.
- `quotientEvaluationHom_injective`: if `[g]` and `[h]` give the same evaluation, every
  `χ ∈ X` has `χ(g⁻¹h) = 1`, so `g⁻¹h ∈ ⁰G` by separation.
- `linearIndependent_quotientEvaluation`: this is Dedekind's independence of characters
  (`linearIndependent_monoidHom`) for the distinct characters `quotientEvaluationHom q` of
  `X`.
- `evaluationAlgHom : ℂ[G ⧸ ⁰G] →ₐ[ℂ] (X → ℂ)` is `MonoidAlgebra.lift` of
  `quotientEvaluation`. It sends `x` to `Σ_q x_q · ev_q` (`evaluationAlgHom_apply`,
  `evaluationAlgHom_apply_apply`) and `of [g]` to `unramifiedEvaluation ν g`
  (`evaluationAlgHom_of`). By linear independence it is injective when `⁰G` is open
  (`evaluationAlgHom_injective`).
- `coeff_invariant`: suppose `evaluationAlgHom x` is invariant under translation by `s ∈ X`.
  Then `s(g) · x_[g] = x_[g]` for every `g`. Proof: since `ev_q(χ s) = ev_q(χ) s(q)`,
  invariance gives `Σ_q (s(q) x_q − x_q) ev_q = 0`, and linear independence makes every
  coefficient zero.
- Fix a subgroup `T` and a set `S ⊆ X` with `g ∈ T ↔ ∀ s ∈ S, s(g) = 1`.
  - `invariant_iff_support` proves that a finitely supported `f` on `G ⧸ ⁰G` satisfies
    `s(g) f([g]) = f([g])` for all `s ∈ S` exactly when `f([g]) ≠ 0` implies `g ∈ T`. If
    `f([g]) ≠ 0`, cancelling gives `s(g) = 1`. Conversely, `g ∈ T` gives `s(g) = 1`.
  - `quotientInclusion : T ⧸ ⁰G.subgroupOf T →* G ⧸ ⁰G` is `QuotientGroup.map` of the inclusion,
    and it is injective (`quotientInclusion_injective`).
  - `exists_invariantAlgHom` takes `Θ = evaluationAlgHom ∘ mapDomainAlgHom quotientInclusion`.
    `Θ` is injective because both factors are. It sends `of [t]` to `unramifiedEvaluation t`.
    Range `⊆`: by `MonoidAlgebra.induction_on`, each `Θ x` lies in
    `unramifiedRegularFunctions` (the generators are evaluations) and is `S`-invariant. On
    generators, `(χ s)(t) = χ(t) s(t) = χ(t)` because `t ∈ T`.
    Range `⊇`: `unramifiedRegularFunctions` is the algebra generated by the evaluations, and
    these are values of `evaluationAlgHom` (`Algebra.adjoin_le`). So an invariant regular
    `φ` equals `evaluationAlgHom x` for some `x`. By `coeff_invariant` and
    `invariant_iff_support`, the support of `x` lies in the range of `quotientInclusion`.
    Hence `x = mapDomain quotientInclusion (comapDomain … x)`
    (`MonoidAlgebra.mapDomain_comapDomain`), and `φ` is in the range of `Θ`.

### The twist stabilizer (`section Rational`)

`twistStabilizer G A` is the subgroup `{ω ∈ X | Nonempty (A ⊗ ω ≅ A)}` of `X`. It contains
`1` (`rationalUnramifiedTwistOneIso`). It is closed under products, by
`rationalUnramifiedTwistMulIso` and twisting an isomorphism with `SmoothRep.twistIso`. It is
closed under inverses: twist `A ≅ A ⊗ ω` by `ω⁻¹`, then use `ω⁻¹ ω = 1`.

## Main theorem `rationalTwistStabilizerKernel`

After the standard setup (affine `G`, smoothness, the canonical topology and topological group
structure on `G(F)`), let `stab = twistStabilizer G A`. The statement's `T` satisfies
`g ∈ T ↔ ∀ s ∈ stab, s(g) = 1` (`Subgroup.mem_iInf` and `MonoidHom.mem_ker`).

1. `⁰G ≤ T`: every unramified character contains `⁰G` in its kernel by definition.
2. `Z(G(F)) ≤ T`: fix `ω ∈ stab` and a central `z`. The operator of `z` is an
   intertwining endomorphism of `A`, so it is a scalar `c` by
   `Schur.rationalPoint_scalarEndomorphism`. The scalar `c` is nonzero because `z` acts
   invertibly on the nontrivial `A`. Apply the isomorphism `A ≅ A ⊗ ω` to a nonzero vector;
   intertwining gives `c = ω(z) c`, so `ω(z) = 1`. This argument repeats the one in
   `rationalTwistStabilizerFinite`.
3. `T` has finite index: `T` contains `⁰G ⊔ Z(G(F))` by items 1 and 2. That subgroup has finite
   index by the published `rationalCommonNormKernel_sup_center_finiteIndex`, so
   `Subgroup.finiteIndex_of_le` applies.
4. `ω ∈ stab ↔ T ≤ ker ω`: the forward direction is `iInf₂_le`. For the reverse direction,
   `stab` is finite by the published `rationalTwistStabilizerFinite`. Apply
   `exists_eq_of_forall_eq_one` to `S = stab` with `emb s = s` viewed as a homomorphism
   `G(F) →* ℂˣ`. An element killed by all of `stab` lies in `T`, hence in `ker ω`. So `ω`
   equals some `s ∈ stab` (`ContinuousMonoidHom.toMonoidHom_injective`).
5. `invariant_iff_support` with `S = stab`.
6. `exists_invariantAlgHom` with `S = stab`, using that `⁰G` is open
   (`isOpen_rationalCommonNormKernel`).

The proof uses no admissibility hypothesis and no unpublished input. Its Library inputs are
`rationalTwistStabilizerFinite`, `rationalCommonNormKernel_sup_center_finiteIndex`,
`Schur.rationalPoint_scalarEndomorphism`, `isOpen_rationalCommonNormKernel`, the twist
isomorphisms of `RationalInertia` and `Category/Twist`, and the published definitions of
unramified characters, `unramifiedEvaluation` and `unramifiedRegularFunctions`.
