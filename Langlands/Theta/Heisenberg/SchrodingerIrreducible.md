# The Schrödinger model is smooth, irreducible and admissible

**GKT §1.2.2** (Theorem 1.13, p. 25: the Schrödinger model is a model of the Heisenberg
representation) and **Proposition 1.29** (p. 35: it is admissible).

The module `Langlands.Theta.Heisenberg.SchrodingerIrreducible` proves that the Schrödinger
representation `schrodingerSB` of `Langlands.Theta.Heisenberg.Schrodinger` is smooth, irreducible
and admissible, so that it is the Heisenberg representation with central character `ψ` (and the
metaplectic group of `Langlands.Theta.Metaplectic.Defs` can be taken in this model).

## Content

Let `F` be a nonarchimedean local field with `⅟2`, `X`, `Y` finite-dimensional `F`-vector spaces
with their module topologies, `β : X →ₗ[F] Y →ₗ[F] F` and `ψ : AddChar F ℂ` continuous.

- `isSmooth_schrodingerSB hψ hβ : IsSmooth (schrodingerSB hψ hβ)`: a Schwartz–Bruhat function is
  invariant under the translations by a neighbourhood of `0`, and the characters `ψ(β(·, y))` are
  trivial on its (compact) support for `y` near `0`; by `isSmooth_of_eventually` the stabilizers
  are open.
- `isIrreducible_schrodingerSB [β.IsPerfPair] hψ hψ1 hβ`: for a perfect pairing and `ψ ≠ 1`, the
  representation is irreducible.
- `isAdmissible_schrodingerSB [β.IsPerfPair] hψ hψ1 hβ`: it is admissible
  (`Langlands.IsAdmissible`: smooth, and the vectors fixed by an open subgroup form a
  finite-dimensional space).

**The proof.** It is not the book's (which identifies the model with the induced model of the
Lagrangian `X`, writing its functions on `H(X)\H(W) ≅ Y`). For the pairing `ψ ∘ β` write `T^⊥` for
the orthogonal, in `Y`, of a set `T ⊆ X` (`orthRight`), and in `X` of a set of `Y` (`orthLeft`).

1. *Lattice pairs.* A `LatticePair β ψ` is a pair of compact open subgroups `L ⊆ X`, `M ⊆ Y` with
   `M = L^⊥` and `L = M^⊥`. It exists (`LatticePair.nonempty`): for a compact open `L₀`, take
   `M = L₀^⊥` and `L = M^⊥`; then `L^⊥ = L₀^⊥⊥⊥ = L₀^⊥ = M`. The orthogonal of a compact set is a
   neighbourhood of `0` (continuity), and the orthogonal of a neighbourhood of `0` is compact: the
   form `((x, y), (x', y')) ↦ β(x, y') + β(x', y)` on `X × Y` is symmetric and non-degenerate, so
   `ψ` of it is a self-dual bicharacter (`isSelfDualBicharacter_of_symm`,
   `Langlands/HarmonicAnalysis/Bicharacter/SelfDual.lean`), whose field `big` says this. A
   continuous character of `F` has values of modulus one (`norm_addChar_eq_one`). The scaled pairs
   `(tL, t⁻¹M)`, `t ∈ Fˣ`, are again lattice pairs (`LatticePair.smul`).
2. *Self-dual data.* For a lattice pair, `A = L × M` is self-dual for `ψ ∘ polarizedForm β`, and
   `ψ_A(l, m) = ψ(½ β(l, m))` splits the cocycle on it: a `SelfDualDatum`
   (`LatticePair.toSelfDualDatum`, of `Langlands.Theta.Heisenberg.InducedModel`).
3. *Eigenvectors.* In the Schrödinger model the `ψ_A`-eigenvectors of `A` are the multiples of
   `1_L` (`LatticePair.eq_indicator_of_eigen`): they are `L`-invariant (the operators of `(l, 0)`
   translate) and supported in `M^⊥ = L` (the operators of `(0, m)` multiply by `ψ(β(·, m))`).
4. *Irreducibility.* The representation is smooth, so every non-zero subrepresentation contains a
   non-zero `ψ_A`-eigenvector for every scaled pair (`SelfDualDatum.exists_eigenvector_mem`),
   hence the indicators `1_{tL}` for all `t`. A Schwartz–Bruhat function `f` is invariant under
   `tL` for `t` small, and is then the finite sum `∑ f(x_c) 1_{tL}(· - x_c)` over the classes `c`
   of its support modulo `tL` (`eq_sum_translates`); the translates are the operators of
   `(-x_c, 0)` applied to `1_{tL}`. So the subrepresentation is everything.
5. *Admissibility.* An open subgroup of the Heisenberg group contains the elements `(u, 0)` with
   `u ∈ tL × (s⁻¹M)` for suitable `t, s`; a vector fixed by them is `tL`-invariant and supported in
   `(s⁻¹ M)^⊥ = sL`, hence in the span of the finitely many translates of `1_{tL}` by the
   representatives of `sL / tL` (the book's proof, with the subgroups `K_n` of a self-dual
   lattice).

Internal declarations are in `Langlands.HeisenbergGroup.SchrodingerIrreducible.Internal`
(`orthRight`, `orthLeft`, `LatticePair`, `symmForm`, and the lemmas above).

## Declarations

- `Langlands.HeisenbergGroup.isSmooth_schrodingerSB`, `isIrreducible_schrodingerSB`,
  `isAdmissible_schrodingerSB`.

## Dependencies

`Langlands.Theta.Heisenberg.InducedModel` (self-dual data, eigenvectors, `isSmooth_of_eventually`),
`Langlands.Theta.Heisenberg.Schrodinger`, `Langlands.HarmonicAnalysis.Bicharacter.Fourier`
(invariance and indicators of Schwartz–Bruhat functions) and, through it,
`Langlands.HarmonicAnalysis.Bicharacter.SelfDual`; Mathlib: `LinearAlgebra.PerfectPairing.Basic`.
