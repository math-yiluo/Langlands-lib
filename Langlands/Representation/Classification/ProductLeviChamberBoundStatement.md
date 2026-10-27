# Chamber bound for matrix coefficients of a product Levi

Author: Worker 246.

This pair defines one closed proposition,
`Langlands.GLProductLeviChamberCoefficientBoundStatement.{uF,uV}`, with
independent field and representation universes. It is a `Prop`-valued
definition; nothing is proved here. It is an internal intermediate statement
for the proof of
[`GLProductLeviTemperedExponentSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md)
in task `ea9d1814-a777-42a1-9bf7-29b9b44dc87e`.

## Exact statement

The proposition quantifies every prime `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, every `T : F.TopologicalData` (with the topology
`T.topology` installed), every rank `n : ℕ` (rank zero is allowed), every
block shape `C : BlockShape n` and every bundled complex representation
`S : Rep.{uV} ℂ (C.Levi F.Carrier)` of the actual product Levi
`M_C = ∏_j GL_(C.size j)(F)`.

Hypotheses:

1. `IsAdmissible S.ρ`. No irreducibility, central character, finite length or
   nonzero carrier is assumed.
2. The upper generalized-exponent hypothesis, copied verbatim from
   `GLProductLeviTemperedExponentSufficiencyStatement`: for every refinement
   `D : BlockRefinement C` and every character
   `ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ` with open kernel that is
   a generalized eigencharacter of `T.normalizedRefinedJacquet C D S.ρ`
   restricted along `flattenedLeviEquiv F.Carrier C D` and
   `(C.flatten D).blockScalarLevi F.Carrier`, one has `‖ψ a‖ ≤ 1` for every
   fine scalar tuple `a` whose normalized absolute values
   `T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩))` are `Monotone` in `i`
   separately within each outer block `j`. The normalized action is the
   unnormalized upper Jacquet action multiplied by the inverse square root of
   the refined modulus.

Conclusion: for every smooth functional `ℓ : SmoothDual S.ρ`, every vector
`v : S` and every real `η > 0` there is a real constant `c` such that

```text
‖matrixCoefficient S.ρ ℓ v (fun j => representative T (lam j))‖
  ≤ c * ∏ j, delta T (lam j) ^ (1/2 - η)
```

for every family `lam : ∀ j : Fin C.length, Fin (C.size j) → ℤ` with
`CartanQuotient.Normalized (lam j)` for every `j`. Here
`matrixCoefficient S.ρ ℓ v g = ℓ (S.ρ g v)`, the Levi element
`fun j => representative T (lam j)` has diagonal blocks
`diag(ϖ^(lam j 0), …)` for the uniformizer `ϖ` specified by `T`, and
`delta T (lam j) = q^(-degree (lam j))` with
`degree μ = ∑_{i<i'} (μ i - μ i')`; see
[`CartanQuotientDefinitions`](../../Group/GL/CartanQuotientDefinitions.md).
`Normalized` means antitone, nonnegative, with some coordinate zero. The
constant may depend on everything except `lam`; it is uniform over the
normalized chamber of every block simultaneously. The power uses `Real.rpow`
of the positive real `delta T (lam j)`.

Since `delta T (lam j) ≤ 1` on the antitone chamber, the bound weakens as `η`
grows; its content is for small `η`. The real-exponent form `δ^(1/2-η)`
replaces the polynomial factor `(1 + σ)^d` of Waldspurger's estimate below and
is what the tempered `L^(2+ε)` conclusion needs: with `η` small compared to
`ε`, `δ^((1/2-η)(2+ε)) δ⁻¹` is summable over the normalized chamber.

## Provenance (derived)

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.
Source ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`. No errata
note for these passages was found in the public Library notes or project
notes.

The implication (ii) ⇒ (i) of Proposition III.2.2 (printed p.266, PDF32)
says that the argument of Corollary III.1.2 (printed pp.263–264, PDF29–30)
bounds every coefficient by `cΞ(g)(1 + σ(g))^r`, the only change being that
one has merely `|χ(a)| ≤ 1` on `Ā₀⁺ ∩ A_M`. In that argument the coefficient
on the closed positive chamber is reduced to functions
`a ↦ δ_P(a)^(1/2) ∑_χ χ(a) Q_χ(H_M(a))` with exponents `χ` of the Jacquet
module. The present statement is the corresponding chamber estimate for the
product Levi `M_C` at the representatives `a(lam)`, in the weakened form
`δ^(1/2-η)` without `Ξ`; it is a derived formulation not stated verbatim by
Waldspurger. The sign conventions agree: the positive chamber of printed
p.239–240 for the upper Borel of each factor is `Antitone`, and its modulus is
`δ₀(a(lam_j)) = delta T (lam_j)`.

## Intended proof (not part of the statement)

Fix a compact open subgroup `K` of `M_C` fixing `v` and `ℓ` with an Iwahori
factorization for every block refinement, and the finite-dimensional space
`V^K`. For antidominant `a` put `A(a) = e_K S.ρ(a)` on `V^K`. Then
`ℓ(S.ρ(a) v) = ℓ(A(a) v)`, `A` is multiplicative on the antidominant monoid,
and `A(a(lam))` is the product of powers of the operators `A_s` attached to
the fundamental coweights `diag(ϖ I_k, I)` in block `j`. A nonzero
eigenvalue `α` of `A_s` lies on its stable image; the Jacquet map is
bijective there for the refinement `(k, C.size j - k)` of block `j`, so
`α` is an eigenvalue of the unnormalized Jacquet action. A common eigenvector
of the block-scalar centre then gives an open-kernel eigencharacter, and the
hypothesis at the scalar `(ϖ, 1)` in block `j` yields
`|α| ≤ δ_s^(1/2)`, `δ_s = q^(-k(C.size j - k))`. Gelfand's spectral-radius
formula gives `‖A_s^m‖ ≤ c_s (δ_s^(1/2-η))^m`, and submultiplicativity gives
the stated bound. All of these steps remain to be proved.
