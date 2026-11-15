# A Nakayama-type lemma for subrings (for Stacks Lemma 11.1)

This module supports the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.1
(Tag 07FG), in `ArtinianFlatSubalgebra`. The declaration is in the namespace
`Langlands.CommutativeAlgebra.Popescu.ArtinianFlat`.

## Declarations

- `mem_subring_of_nilpotent R J hN S hSR hSJ hJ hR b`. Let `B` be a commutative ring, `R` a
  subring, and `J` an ideal with `J^N = 0`. Assume there is a set `S ⊆ R ∩ J` with
  `J ⊆ (S)`, and that every `b ∈ B` is congruent mod `J` to an element of `R`. Then
  `R = B`.
  **Proof.**
  1. Every `y ∈ (S)` is congruent mod `J²` to some `r ∈ R ∩ J`. By induction on
     `y ∈ span S`: for `y = a s` with `a ≡ r_a (mod J)` and `r_a ∈ R`, take `r_a s`.
  2. For every `t`, every `y ∈ Jᵗ` is congruent mod `J^{t+1}` to some `r ∈ R ∩ Jᵗ`. This is
     induction on `t`, using `J^{t+1} = Jᵗ J`, `Submodule.mul_induction_on` and step 1.
  3. Hence every `b` is congruent mod `Jᵗ` to an element of `R`, for all `t`. Take `t = N`.

It is applied directly twice:

- to show that `κ[x₁, …, x_d] → B`, `xᵢ ↦ tᵢ`, is surjective (`eval₂_surjective` in
  `ArtinianFlatClaim`). That lemma is in turn used in the inductive step of the claim
  (`coeffClaim_of_surjective`) and in the main proof (`artinianFlatSubalgebra`);
- to show that the subalgebra `A` is a localization of a finitely generated `k`-algebra
  (`essFiniteType_of_residue` in `ArtinianFlatConstruction`).

## Source

Internal lemma; no single statement in the source. Stacks Project, *Smoothing Ring Maps*
(`smoothing.pdf` in `stacks-artin-axioms-approximation-2026-11-06`), proof of Lemma 11.1
(Tag 07FG, printed pp. 25-26), uses its instances without comment: `Ψ_σ` is surjective, and
the algebras are "essentially of finite type over `k` by Algebra, Lemma 54.4".
