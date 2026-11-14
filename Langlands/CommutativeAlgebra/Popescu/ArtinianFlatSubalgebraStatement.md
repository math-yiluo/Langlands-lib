# Artinian local algebras as unions of flat essentially finite type subalgebras

`Langlands.CommutativeAlgebra.Popescu.ArtinianFlatSubalgebraStatement` (universe `u`). Let `k` be a
field of characteristic `p > 0` and `L` an Artinian local `k`-algebra with residue field `κ_L` such
that `H₁(L_{κ_L/k})` is finite-dimensional over `κ_L`
(`Module.Finite (ResidueField L) (Algebra.H1Cotangent k (ResidueField L))`). Then every finite
subset `E ⊂ L` is contained in a `k`-subalgebra `A ⊂ L` (`A : Subalgebra k L`) such that

- `A` is a local ring and an Artinian ring;
- `A` is essentially of finite type over `k` (`Algebra.EssFiniteType k A`);
- `L` is flat over `A`;
- `𝔪_A L = 𝔪_L`: `(maximalIdeal A).map (algebraMap A L) = maximalIdeal L`.

## Source

Stacks Project, Smoothing Ring Maps, Lemma 16.11.1 (Tag 07FG); source
`stacks-artin-axioms-approximation-2026-11-06`, smoothing.pdf, printed p. 25: "Let `k` be a field
of characteristic `p > 0`. Let `(Λ, 𝔪, K)` be an Artinian local `k`-algebra. Assume that
`dim H₁(L_{K/k}) < ∞`. Then `Λ` is a filtered colimit of Artinian local `k`-algebras `A` with each
map `A → Λ` flat, with `𝔪_A Λ = 𝔪`, and with `A` essentially of finite type over `k`." Its proof
begins: "the flatness of `A → Λ` implies that `A → Λ` is injective, so the lemma really tells us
that `Λ` is a directed union of these types of subrings `A ⊂ Λ`." It is used in this form in the proof of
Lemma 16.11.2 (Tag 07FH): "Pick `A ⊂ Λ̄` containing `E` such that `A` is local Artinian, essentially
of finite type over `k`, the map `A → Λ̄` is flat, and `𝔪_A` generates the maximal ideal of `Λ̄`,
see Lemma 11.1."

## Encoding

- "`Λ` is a filtered union of such subalgebras" is encoded by its consequence used in Lemma
  16.11.2: every finite subset lies in one of them. The proof of Lemma 16.11.1 gives this directly.
  The subalgebras `Ψ_σ(F[x₁, …, x_d]/(g))` grow with the finitely generated field `F`, and each
  element of `Λ` lies in one of them once `F` contains finitely many coefficients.
- `Algebra.H1Cotangent k κ_L` is Mathlib's `H¹` of the naive cotangent complex. It agrees with
  `H₁(L_{κ_L/k})` (Stacks Tag 08RA).
- All types are in one universe `u`.
