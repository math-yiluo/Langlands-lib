# The transfer law for the Tits obstruction in coset-sum form

This module states the transfer law of Task 7603 (clause 3) for an intermediate field `E` of
`K / k`, with the coset sum of `SimplyConnected/StarFixedWeights`. It then specializes the law
to the simple-vertex field of a Tits index (clause 4). The Brauer-level content is the
transfer theorem `GaloisPinningData.titsObstructionValue_transfer` of `Reductive/TitsTransfer`.
That theorem is stated for an enumeration of the embeddings of `E` into a finite Galois
extension `N` and for extensions of these embeddings to `K`. This module supplies those choices
and identifies the embedding-indexed sum with the coset sum.

Throughout, `k` and `K` are fields in one universe `u`, and `E : IntermediateField k K`. The
corestriction is the Library's `corHom k E : BrauerGroup E →+ BrauerGroup k`
(`Algebra/BrauerCorestriction/Hom`, Task 7575). It needs `E / k` finite and separable, and
no other hypothesis on `k`. In particular no result here assumes `k` infinite. The extension
`K / k` is any Galois extension; clause 3 of the task is the case `K = SeparableClosure k`.

## Embeddings and a transversal of `Gal(K/E)`

Assume `K / k` is normal. Let `N = normalClosure k E K` be the normal closure of `E / k`
inside `K` (Mathlib's `IntermediateField.normalClosure`).

* `embeddingLift E σ : K ≃ₐ[k] K`, for `σ : E →ₐ[k] N`. It is Mathlib's
  `AlgHom.liftNormal` of `σ` to `K`. That map is an endomorphism of the algebraic extension
  `K / k`, so it is bijective (`Algebra.IsAlgebraic.algHom_bijective`).
  `embeddingLift_algebraMap` and `embeddingLift_coe` state that it extends `σ`:
  `embeddingLift E σ x = σ x` for `x ∈ E`.
* `embeddingLift_inv_mul_mem_fixingSubgroup_iff`: `(embeddingLift E σ)⁻¹ * g` lies in
  `Γ_E = E.fixingSubgroup` iff `g x = σ x` for every `x ∈ E`.
* `embeddingLift_injective`: distinct embeddings have distinct extensions.
* `isComplement_range_embeddingLift`: the extensions form a left transversal of `Γ_E` in
  `Gal(K/k)` (`Subgroup.IsComplement (Set.range (embeddingLift E)) Γ_E`). Injectivity on
  cosets is the previous criterion. For surjectivity, every `g ∈ Gal(K/k)` restricts on `E` to
  an embedding with values in `N` (Mathlib's `normalClosure.algHomEquiv`). The extension of
  that embedding lies in the coset `g Γ_E`.

Assume moreover that `K / k` is Galois. Then `E / k` is separable.

* `card_embeddings`: `Nat.card (E →ₐ[k] N) = [E : k]`. The proof turns embeddings into `N` into
  embeddings into `K` (`normalClosure.algHomEquiv`). Their number is the separable degree,
  because every minimal polynomial over `k` of an element of `E` splits in the normal
  extension `K` (`Field.finSepDegree_eq_of_adjoin_splits`). The separable degree is `[E : k]`
  because `E / k` is separable. The lemma has no finiteness hypothesis on `E / k`. It is used
  below for finite `E / k`.
* For `E / k` finite: `finite_embeddings` (an instance), and `embeddingEnum E`, an
  enumeration `(E →ₐ[k] N) ≃ Fin ([E : k] - 1 + 1)`.

## The coset sum as a sum over embeddings

For Galois pinning data `d : GaloisPinningData k K G` of an affine group scheme `G` over
`Spec k`, locally of finite type:

* `sum_embeddingLift_eq_cosetSum`: let `λ` be fixed by the star action of `Γ_E`. Then for
  every enumeration `e : (E →ₐ[k] N) ≃ Fin (m + 1)`,
  `∑ i, (d.starAction (embeddingLift E (e.symm i))) • λ = d.cosetSum E λ`. This is the
  Library's `sum_transversal_eq_cosetSum` applied to the transversal above.
* `embeddingConjSum_embeddingLift`: the same identity written with the sum
  `d.embeddingConjSum e (embeddingLift E) λ` of `Reductive/TitsTransfer`.

The coset sum `d.cosetSum E λ = ∑_{σ ∈ Γ/Γ_E} σ ⋆ λ` takes one representative in each left
coset of `Γ_E` and counts a weight again when different cosets give the same weight. When
`Γ_E` is smaller than the stabilizer `Stab(λ)` of `λ`, the coset sum is
`[Stab(λ) : Γ_E]` times the sum over the distinct elements of the star orbit of `λ`
(Library `cosetSum_eq_relIndex_smul`).

## The transfer law

* `isSimplyConnected_baseChange`: the base change `G_E` of a simply connected `G` is simply
  connected. This is the Library's `isSimplyConnectedFieldExtension`.
* `titsObstruction_cosetSum` (clause 3): assume `K / k` Galois, `G` simply connected, `E / k`
  finite, and `λ ∈ d.fixedWeights Γ_E`. Then

  `d.titsObstruction hG ⟨d.cosetSum E λ, _⟩ =
    corHom k E ((d.baseChange E).titsObstruction hG_E (d.fixedWeightsBaseChangeEquiv E λ))`.

  The left side is the obstruction `α_{G,k}` of `G` at the coset sum `∑_{σ ∈ Γ/Γ_E} σ ⋆ λ`.
  That sum is star fixed by the Library's `cosetSum_mem_starFixedWeights`. On the right,
  `d.fixedWeightsBaseChangeEquiv E λ` is the base-changed weight `λ_E = d.weightTransport E λ`.
  It is a star-fixed weight of the base change `d.baseChange E : GaloisPinningData E K G_E`
  (`SimplyConnected/StarFixedWeightsBaseChange`). The right side is `Cor_{E/k}` of the
  obstruction `α_{G_E,E}(λ_E)`.

  Proof: apply `titsObstructionValue_transfer` with `N = normalClosure k E K` (finite and
  Galois over `k`), the count `card_embeddings`, the enumeration `embeddingEnum E` and the
  extensions `embeddingLift E`. The coroot-span hypotheses for `d` and for `d.baseChange E`
  come from simple connectedness of `G` and of `G_E`
  (`corootSpan_eq_top_of_simplyConnected`). The star-fixedness of `λ_E` over `E` comes from
  `weightTransport_mem_starFixedWeights_iff`. Finally `sum_embeddingLift_eq_cosetSum`
  rewrites the embedding-indexed sum of the transfer theorem as the coset sum.

  Independence of choices: the left side involves no choice. `d.cosetSum E λ` is a sum over
  the quotient `Γ/Γ_E`, and every transversal gives it (Library
  `sum_transversal_eq_cosetSum`). The normal closure, the enumeration and the extensions are
  used only inside the proof.
* `titsObstruction_comp_cosetSumHom`: the same identity, with the right side written as the
  composite `corHom k E ∘ α_{G_E,E} ∘ fixedWeightsBaseChangeEquiv E` applied to `λ`.

## Specialization to the simple-vertex field (clause 4)

Let `G` be an affine group scheme over `Spec K`, locally of finite type and simply connected
(`hsc`). Let `d : TitsIndexData G` be a Tits index whose Galois pinning data `d.pinning` live
over `SeparableClosure K`. Let `a` be a simple vertex with simple-vertex field
`k_a = d.starVertexField a`. This field is finite over `K` (Library instance
`finiteDimensional_starVertexField`). Write `ϖ_b = d.absoluteFundamentalCharacter hsc b` for
the actual fundamental weights.

* `finsum_orbit_mem_starFixedWeights`: the sum `∑ᶠ b ∈ O(a), ϖ_b` over the star orbit `O(a)`
  of `a`, each vertex once, is star fixed. It equals the coset sum of `ϖ_a` over `k_a`
  (Library `cosetSum_starVertexField`), which is star fixed.
* `titsObstruction_finsum_orbit`:

  `d.pinning.titsObstruction hsc ⟨∑ᶠ b ∈ O(a), ϖ_b, _⟩ =
    corHom K k_a ((d.pinning.baseChange k_a).titsObstruction _
      (d.pinning.fixedWeightsBaseChangeEquiv k_a ⟨ϖ_a, _⟩))`.

  `ϖ_a` is fixed by `Gal(K^sep / k_a)` (Library
  `absoluteFundamentalCharacter_mem_fixedWeights`). The identity is `titsObstruction_cosetSum`
  for `E = k_a` and `λ = ϖ_a`, combined with `cosetSum_starVertexField`. That lemma equates the
  coset sum with the orbit sum, each vertex once. It rests on a proved comparison of
  stabilizers (Library `equivStabilizer_absoluteFundamentalCharacter`): the star stabilizer
  of the weight `ϖ_a` is the vertex stabilizer of `a`, whose fixed field is `k_a`. So every
  multiplicity `[Stab(ϖ_a) : Gal(K^sep / k_a)]` is `1`. No central-character stabilizer is
  used or identified with the vertex stabilizer.

## Provenance

Derived. The results are integral-weight statements required by clauses 3 and 4 of
Task 7603. They are not the transfer proposition of Tits (1971).

* Tits (1971), Proposition 5.1 (printed p. 207), concerns the homomorphism
  `β_{G,k} : C*^Γ → Br k` on Galois-invariant central characters. For `c₁ ∈ C*` with exact
  stabilizer `Γ₁` in `Γ`, fixed field `k₁` and a system `Θ` of representatives of `Γ/Γ₁`,
  it states `β_{G,k}(Σ_{θ∈Θ} θ(c₁)) = Cor_{k₁/k}(β_{G,k₁}(c₁))`.
* By Corollary 3.5 (printed p. 205), the homomorphism `α_{G,k} : Λ^Γ → Br k`, which extends
  the obstruction on invariant dominant weights, is the composite of the canonical
  projection `Λ^Γ → C*^Γ` with `β_{G,k}`.

The identity here is a derived analogue for integral weights:
`α_{G,k}(Σ_{σ ∈ Γ/Γ_E} σ ⋆ λ) = Cor_{E/k}(α_{G_E,E}(λ_E))`. Here `E` is any finite
intermediate field such that `Γ_E` fixes `λ`. It is not deduced from Proposition 5.1, and
the two statements have different domains:

* `Γ_E` may be smaller than `Stab(λ)`, and the coset sum then has multiplicities (see above).
* `Stab(λ)` may be smaller than the stabilizer of the central character of `λ`.

For example, take split `SL₂` over `ℚ`, `E = ℚ(√2)` and `λ` the fundamental weight. The coset
sum is `2λ`, whose central character is trivial. The central character of `λ` is the
nontrivial character of `μ₂`, with stabilizer `Γ` and `k₁ = ℚ`. For the clause-4
specialization the stabilizer of `ϖ_a` is proved to be the vertex stabilizer, so the coset
sum is the orbit sum of `ϖ_a` without multiplicities. The stabilizer of the central character
of `ϖ_a` can still be larger, and this module makes no claim about it.

The Brauer identity is `titsObstructionValue_transfer` of `Reductive/TitsTransfer`, whose
Markdown explains its matrix-level proof. This module adds the field-theoretic choices (normal
closure, enumeration, extensions to `K`, transversal), the identification with the coset sum,
and the vertex specialization. Mathlib supplies the facts about normal closures, liftings to
normal extensions and separable degrees named above.
