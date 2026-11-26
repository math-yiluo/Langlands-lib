# Proof of BK93 (2.3.12): a split derived stratum obstructs field generation

`Langlands.BushnellKutzko.PureApproximation.splitObstructionPremise` proves the published
proposition `Langlands.BushnellKutzko.PureApproximation.SplitObstructionPremise` in its three
universes `uF, uV, uE`, with no further hypotheses. The source is C. J. Bushnell and
P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), registered as
`bushnell-kutzko-1993-admissible-dual-gln`: Proposition (2.3.12), printed p. 61, with proof on
printed pp. 61–64 (PDF pp. 73–76).

Statement. Let `S = [𝔄, n, r, β]` be a stratum, `b` an endomorphism, `s` a tame corestriction
relative to `E/F` and `D` a stratum over `𝔬_E` with `S.IsDerivedStratum E b s D`: `S` is
simple, `E = F[β]` acts as in `IsGeneratedField`, `b ∈ 𝔓^{−r}`, and `D = [𝔅, r, r−1, s(b)]`
on the same lattices. If `D.IsSplit`, then `¬ IsField (elementAlgebra (S.b + b))`.

## The implemented proof

Write `A = End_F(V)`, `B = End_E(V)`, `𝓛 = S.chain` and `a = s b`.

1. **Setup.** The units of `E` normalize `𝓛` (`normalizingUnits_of_isField`), and
   `E/F` is finite (`LatticeChain.finiteDimensional_subfield`). Since `D` uses the lattices of
   `𝓛`, `x ∈ 𝔔^n` for `D.chain` iff `x.restrictScalars F ∈ 𝔓^n`. By the published
   `tameCorestriction`, `s` maps `𝔓^j` into `𝔔^j` and is surjective. In particular
   `a ∈ 𝔔^{−r}`.
2. **Idempotents over `E`.** `exists_split_idempotents` (module
   `SplitObstructionIdempotents`) gives complementary nonzero idempotents `e₁, e₂ ∈ 𝔅`
   commuting with `a`, with graded injectivity on `e₁Be₂`. On the finite-dimensional
   `E`-space `e₁Be₂` the map `x ↦ a x − x a` is injective, by separation, hence surjective.
   Graded injectivity then places the preimage of an element of `𝔔^{j−r}` in `𝔔^j` (`hB`).
   This is the property of the splitting (2.3.8)(iii) used in (2.3.13).
3. **Exactness.** If `y ∈ 𝔓^j` and `s y = 0`, then `y = β w − w β` for some
   `w ∈ 𝔓^{j+r+1}`. If `β ∈ F`, then `ker s` is the image of `a_β = 0`
   (`TameCorestriction.range_adjointMap_eq_ker`). Otherwise this is the third exact sequence
   of the published `adjointExactness` (BK93 (1.4.10)) with `k = −r−1 ≥ k₀(β, 𝔄)`.
4. **Lemma (2.3.13).** Put `εᵢ = eᵢ.restrictScalars F` and let `D_γ` be the block commutator
   of `γ = β + b`. On `ε₁Aε₂`, `D_γ x = (βx − xβ) + (ε₁bε₁x − xε₂bε₂)`. Take
   `y ∈ 𝔓^{i−r} ∩ ε₁Aε₂`. Then `s y ∈ 𝔔^{i−r} ∩ e₁Be₂`, and step 2 gives `z ∈ 𝔔^i ∩ e₁Be₂`
   with `a z − z a = s y`. The bimodule laws of `s`, together with the centrality of `s(β)`
   in `B`, give `s(D_γ z) = a z − z a`. So `y − D_γ z` lies in `ker s ∩ 𝔓^{i−r}`. By step 3 it
   is `βw − wβ` with `w ∈ 𝔓^{i+1}`, and `x' = ε₁ w ε₂` satisfies
   `y − D_γ(z + x') ∈ 𝔓^{i+1−r} ∩ ε₁Aε₂`. Nakayama's lemma
   (`SplitObstruction.blockFiltration_surjective`) upgrades this to surjectivity on every
   step, as in Corollary (2.3.15).
5. **(2.3.14).** Since `s(ε₁ b ε₂) = e₁ a e₂ = 0`, step 3 makes `ε₁ γ ε₂ = ε₁ b ε₂`
   congruent modulo `𝔓^{1−r}` to the block commutator of an element of `𝔓^1 ∩ ε₁Aε₂`.
   Moreover `ε₂ γ ε₁ = ε₂ b ε₁ ∈ 𝔓^{−r}`.
6. **Conclusion.** `SplitObstruction.not_isField_of_blockCommutator` (module
   `SplitObstructionRiccati`) conjugates `γ` to block-triangular form and shows that `F[γ]` is
   not a field.

## Differences from the source route

- The source first coarsens the chain to `gcd(r, e_β) = 1`, so that the splitting of [K4]
  (3.4) applies. Here graded injectivity comes directly from an idempotent in `𝔬_E[y_b]`,
  for any `r` (step 2 and `SplitObstructionIdempotents`).
- The source passes from graded surjectivity to (2.3.15) by a completeness argument; here
  this is Nakayama's lemma (step 4).
- The source builds the conjugating element by successive conjugations; here it is a
  contraction fixed point (`SplitObstructionRiccati`). The source then concludes by (2.3.5);
  here an `F[γ']`-linear map gives a nonzero kernel element.

The proof uses neither BK93 (2.4.1)(i) nor its Library form
`PureStratumSimpleApproximationStatement`.
