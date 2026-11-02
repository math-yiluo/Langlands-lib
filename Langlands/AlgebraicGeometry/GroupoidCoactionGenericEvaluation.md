# Generic evaluation for coactions induced from a finite faithfully flat cover

Module `Langlands.AlgebraicGeometry.GroupoidCoactionGenericEvaluation`, namespace
`Langlands.AlgebraicGeometry.GroupoidCoaction`. It imports the Library modules
`GroupoidCoactionInvariantIdeal`, `GroupoidCoactionCokernel`, `GroupoidCoactionInduced` and
`GroupoidCoactionPushforward` (which bring in the kernel and Hom coactions).

This module is a ring-level ingredient for the comodule proof of the Noetherian case of
finite-surjective affine descent (Stacks, Cohomology of Algebraic Spaces, Lemma 69.17.3,
Tag 07VP). It was written for the Key proof task 74e16b76 (Worker 148), and in the end for this
task (Tag 07VS). Source: the registered folder `stacks-noetherian-space-affine-descent-2026-11-01`,
page `07VP.html`.

## Setting

All rings are commutative and live in one universe `u`.

- `t : B →+* C` with `hE : RingEtaleEquivalenceRelation t` is an affine étale equivalence
  relation (the ring form of `R ⇉ U`).
- `td : D →+* P` with `hP : RingEtaleEquivalenceRelation td` is a second one. Together with
  `e : P ≃ₐ[D] D ⊗[B] C` and `ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D)` it is
  a source-cartesian cover of the first relation: the ring form of `Y ×_X U` over `U`. The ring
  `P` also carries the compatible `B`-algebra structure (`[Algebra B P] [IsScalarTower B D P]`).
- `A = invariantRing td` is the invariant subring of `D`. The hypotheses
  `[Module.FaithfullyFlat A D]`, `ε : P ≃ₐ[D] D ⊗[A] D` and `hε : ∀ d, ε (td d) = 1 ⊗ₜ d` say that
  the covering relation is effective with affine quotient `Spec A`, that is `Y = Spec A`.
- For a prime `q` of `A`, `G = D ⊗[A] (A ⧸ q)` is the ring form of the pullback to `U` of
  `f'_* 𝒪_{Z'}`, where `Z' = V(q) ⊆ Y` is integral. Through the pushed-forward induced coaction
  `pushforward e ht (induced td (A ⧸ q)) hE hP`, it is a module on the relation `t`.

## Declarations

- `piCoactionMap`, `piCoaction θ : GroupoidCoaction t (ι → M)`: the coordinatewise coaction on a
  finite product `ι → M`, for `[Fintype ι] [DecidableEq ι]`. Its value at `f` is
  `∑ i, (C ⊗ single i) (θ (f i))`. The counit law reduces to that of `θ`; the cocycle law reduces
  to the Library lemma `coactionCompose_map`, applied to `single i`. Supporting lemmas:
  `piCoactionMap_apply`, `piCoactionMap_smul`, `piCoactionMap_single`, `lTensor_pi_eq_sum`.
- `isHom_pi`: a family of equivariant maps `f i : N → M` gives an equivariant map
  `LinearMap.pi f : N → (ι → M)` into the product coaction.
- `exists_smul_eq_zero_of_forall`: a finite module over `B` in which every element is killed by an
  element outside a prime `p` is killed by a single element outside `p`. The proof uses the module
  support (`Module.notMem_support_iff'` and `Module.mem_support_iff_of_finite`).
- `exists_generic_basis`: let `B` be Noetherian and reduced, `G` a finite `B`-module spanned by a
  family `v`, `p` a minimal prime, and `v x₀` an element not killed by any element outside `p`. Then
  there are `r > 0`, indices `a : Fin r → α` and `s ∉ p` such that, for
  `φ = Fintype.linearCombination B (v ∘ a)`, `s • g ∈ range φ` for every `g` and `s • x = 0`
  for every `x ∈ ker φ`. Proof: `B_p` is a field (`Ring.KrullDimLE.isField_of_isReduced`). The
  localized values span `G_p`, and a linearly independent subfamily spanning `G_p`
  (`exists_linearIndependent'`) is finite. It is nonempty because `v x₀` does not vanish in `G_p`.
  Linear independence shows that each kernel element is killed by a product of denominators.
  Surjectivity of the localized map shows that each cokernel element is killed by an element
  outside `p`. Two applications of `exists_smul_eq_zero_of_forall` then give `s = s₁ * s₂`.
- `evaluation_annihilators`: let `g : Fin r → G` satisfy the two conclusions above for `s`. Then
  for evaluation `Ev = LinearMap.pi (fun i => applyₗ (g i)) : (G →ₗ[B] H) →ₗ[B] (Fin r → H)`,
  `s` kills `ker Ev` and `s * s` kills `coker Ev`. For the kernel: if `ψ (g i) = 0` for all `i`,
  then `s • ψ y = ψ (s • y) = 0`, because `s • y` lies in the span. For the cokernel: given
  `h : Fin r → H`, the map `s • (linearCombination h)` vanishes on `ker φ`. It therefore factors
  through `range φ`, and precomposing with `s • id : G → range φ` gives `ψ` with
  `ψ (g i) = (s * s) • h i`.
- `finite_linearMap_of_isNoetherianRing`: over a Noetherian ring, `G →ₗ[B] H` is finite for finite
  `G` and `H`. Restriction along a surjection `(Fin n → B) → G` embeds it into a finite module.
- `span_range_algebraMap_eq_top`: in the setting above, `D` is spanned over `A` by the image of
  `B`. Proof: let `S₀` be that span. Under `e` and `ε`, `D ⊗[B] C ≅ D ⊗[A] D`, and the elements
  `1 ⊗ t b` map to `1 ⊗ algebraMap B D b`. Since `C` is spanned over `B` by `range t` (the field
  `adjoin_range_eq_top` of `RingEtaleEquivalenceRelation`), the `D`-linear map
  `D ⊗[B] C → D ⊗[A] (D ⧸ S₀)` vanishes. Hence `D ⊗[A] (D ⧸ S₀) = 0`, and faithful flatness of `D`
  over `A` gives `S₀ = ⊤`.
- `span_range_one_tmul_eq_top`: consequently, for every `A`-module `N`, `D ⊗[A] N` is spanned over
  `B` by the elements `1 ⊗ n`.
- `finite_tensor_quotient`: if `D` is finite over `B`, so is `D ⊗[A] (A ⧸ q)`. The map
  `d ↦ d ⊗ 1` is `B`-linear and surjective.
- `genericEvaluation B td q a H` (the selected definition): for `a : Fin r → A ⧸ q` and a
  `B`-module `H`, the `B`-linear evaluation
  `((D ⊗[A] (A ⧸ q)) →ₗ[B] H) →ₗ[B] (Fin r → H)`, `ψ ↦ (ψ (1 ⊗ a i))ᵢ`. Its value is recorded by
  the simp lemma `genericEvaluation_apply`.
- `pushforward_induced_one_tmul_mem_invariants`: the elements `1 ⊗ n` of the pushed-forward
  induced module are invariant.
- `exists_genericEvaluation` (main theorem). Assume, in addition to the setting above, that `B` is
  Noetherian, reduced and nonzero, that `D` is finite over `B` and that
  `PrimeSpectrum.comap (algebraMap B D)` is surjective. Let `H` be a finite `B`-module with a
  coaction `θH`. Then there exist a prime `q` of `A`, an integer `r > 0`, elements
  `a : Fin r → A ⧸ q` and an ideal `I` of `B` with:
  - `I ≠ ⊥` and `I` is invariant (`IsInvariantIdeal t I`);
  - `D ⊗[A] (A ⧸ q)` is a finite `B`-module;
  - `I ≤ radical (Ann (ker (genericEvaluation B td q a H)))`;
  - `I ≤ radical (Ann (coker (genericEvaluation B td q a H)))`.

## Proof of the main theorem

Choose a maximal ideal, then a minimal prime `p` of `B` below it. By surjectivity on spectra pick
a prime `Q` of `D` over `p`, and let `q = Q ∩ A`. The element `1 ⊗ 1` of `G = D ⊗[A] (A ⧸ q)` is
not killed by any `c ∉ p`, because `G → D ⧸ Q` sends `c • (1 ⊗ 1)` to the class of `c`.
`exists_generic_basis`, applied to the spanning family `x ↦ 1 ⊗ x`, gives `r > 0`, `a` and `s ∉ p`.
`evaluation_annihilators` then shows that `s` kills `ker Ev` and `s * s` kills `coker Ev`, where
`Ev = genericEvaluation B td q a H`.

The elements `1 ⊗ a i` are invariant, so `Ev` is equivariant from the Hom coaction
`hom hE θG θH` to `piCoaction θH` (`hom_eval_isHom`, `isHom_pi`). All modules involved are finite,
hence finitely presented, over the Noetherian ring `B`. The kernel and cokernel therefore carry
coactions (`kernel`, `cokernel`), and their annihilators are invariant ideals
(`annihilator_isInvariantIdeal`). Take `I = Ann (ker Ev) * Ann (coker Ev)`. This ideal is
invariant (`IsInvariantIdeal.mul`) and lies in both annihilators, hence in their radicals. It
contains `s * (s * s)`, which is not in the prime `p`, so `I ≠ ⊥`.

## Provenance and relation to the literature

Provenance: derived (internal ring-level form). The proof of Tag 07VP verifies condition (3) of
Lemma 69.14.5 for `𝒢 = f'_* 𝒪_{Z'}`, where `Z' → Z` is the finite surjective morphism of
Lemma 69.17.1 over an integral closed subspace `Z ⊆ X`. The Key proof task replaces sheaf
cohomology on `X` with comodules over an affine étale presentation. In that setting, the generic
part of the dévissage needs, for a coherent `ℋ`, an evaluation map `Hom(𝒢, ℋ) → ℋ^{⊕r}` that is
an isomorphism away from a proper invariant closed subset. This module supplies that statement in
ring form:

- `B` is the ring of the étale chart `U` of the (reduced) space and `D` that of `Y ×_X U`;
- `Spec (A ⧸ q)` plays the role of `Z'`;
- `G` is the pullback of `f'_* 𝒪_{Z'}` to `U`;
- "an isomorphism away from `V(I)` with `I` a nonzero invariant ideal" is expressed by `I`
  lying in the radicals of the annihilators of the kernel and cokernel.

Stacks works with an irreducible `Z` and the generic point of `Z`. Here no irreducibility of the
invariant ring is assumed: one minimal prime `p` of `B` and one element `s ∉ p` suffice, and the
ideal `I` is built from the annihilators themselves. The statement does not claim that `V(I)` is
proper in any irreducible component other than the one through `p`. The choice of `q` from a
prime over a minimal prime of `B` and the explicit annihilator ideal are internal design choices
of this formalization, made to match the interface of the Key task.
