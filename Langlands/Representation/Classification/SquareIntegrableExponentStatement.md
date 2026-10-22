# Casselman's exponent criterion for square-integrability on `GL_n`

Worker 19 states `Langlands.GLSquareIntegrableExponentCriterionStatement`.
This is a proposition definition. It asserts no Lean proof. Square-integrability
is Worker 23's analytic predicate `T.IsSquareIntegrable`, and the exponents are
Worker 23's `T.IsJacquetExponent`. Neither is defined through the other.

## Objects and quantifiers

The statement quantifies every prime `p`, every `PadicField p` `F` in a field
universe `uF`, every realization `T : F.TopologicalData` of its topology, and
every positive rank `n`. The group is the actual
`GeneralLinear n F.Carrier = GL_n(F)`, with the topology induced by `T`.

The representation carrier `V` is a complex vector space in an independent
universe `uV`. It must be nonzero (`Nontrivial V`), and has no topology or
finite-dimensionality assumption. The representation `ρ` must be admissible for
the topology of `T` (`IsAdmissible ρ`, which includes smoothness).

`ω : F^× →* ℂ^×` is an arbitrary group homomorphism. No continuity or unitarity
is assumed. The hypothesis
`∀ a v, ρ (GeneralLinear.scalar a) v = ω a • v` says that `ρ` is an
`ω`-representation: the scalar matrix `a · 1_n` acts by the number `ω(a)`.

## The equivalence

Under these hypotheses, `T.IsSquareIntegrable ρ` holds if and only if both of
the following hold.

- **(a)** `‖ω(a)‖ = 1` for every `a ∈ F^×`.
- **(b)** For every ordered block shape `B = (n_1, …, n_k)` of `n`, every
  character `χ : (F^×)^k →* ℂ^×` with `T.IsJacquetExponent B ρ χ`, and every
  `a = (a_1, …, a_k) ∈ (F^×)^k` such that
  - `|a_1| ≤ |a_2| ≤ ⋯ ≤ |a_k|` (`Monotone` in the index), and
  - `|a_i| ≠ |a_j|` for some `i, j`,

  one has `‖χ(a)‖ < 1`.

Here `|·|` is the published residue-normalized absolute value
`T.normalizedAbs`, with `|ϖ| = q⁻¹`.

The two sides mean the following.

- `T.IsSquareIntegrable ρ` (module `Langlands.Representation.Classification.Tempered`)
  requires `IsSquareIntegrableModCenter ρ μ` for every Borel Haar measure `μ` on
  the actual quotient `GL_n(F) ⧸ Z`. That predicate asks for admissibility, a
  `UnitaryCentralCharacter ρ` (a character of the centre with open kernel and
  norm one by which the centre acts), and membership of every descended
  coefficient norm `gZ ↦ |ℓ(ρ(g) v)|`, for `ℓ` in the smooth dual and `v ∈ V`,
  in `L²(μ)`.
- `T.IsJacquetExponent B ρ χ` (module `Langlands.Representation.Exponents.Jacquet`)
  says that `χ` has open kernel and that, for some `k`, some nonzero vector of
  the normalized Jacquet module of the standard upper block parabolic `P_B` is
  killed by `(a · − χ(a))^k` for every block scalar
  `a = diag(a_1 1_(n_1), …, a_k 1_(n_k))`. The action is the published
  normalized one, `a · [v] = δ_(P_B)(a)^(-1/2) [ρ(a) v]`. On block scalars the
  published block modulus is `δ_(P_B)(a) = ∏_(i<j) |a_i / a_j|^(n_i n_j)`.

## Original source

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995:

- Literature ID: `casselman-1995-admissible-representations`.
- SHA256:
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Printed and PDF page numbers coincide.

Theorem 4.4.6, p.45: "Let ω be a character of Z_G. If (π, V) is an admissible
ω-representation of G, then it is square-integrable if and only if (a) ω is
unitary; (b) for every Θ ⊆ ∆, if χ is a central character of π with respect to
P_Θ then |χ δ_∅^(-1/2)(a)| < 1 for all a ∈ A_Θ^- ∖ A_∅(O)A_∆."

The other passages used are:

- §1.4, p.13: `A_Θ^-(ε)` is the set of `a ∈ A_Θ` with `|α(a)| ≤ ε` for all
  `α ∈ ∆ ∖ Θ`, and `A_Θ^- = A_Θ^-(1)`.
- §1.5, p.16: `δ_P(p) = |det Ad_n(p)|`, with Lemma 1.5.1 and Prop. 1.5.2
  (double-coset volumes for an assigned Haar measure).
- Prop. 2.1.9, p.21: the spaces `V_(χ,n)` and `V_(χ,∞)` of generalized
  central characters.
- §2.5, p.28: the definition of square-integrability for an admissible
  `ω`-representation, which includes `|ω| = 1`.
- pp.44–45, before Theorem 4.4.6: the central characters of `π` with respect
  to `P` are the restrictions to `A` of the characters `χ` of the centre of `M`
  with `(V_N)_(χ,∞) ≠ 0`. For an `ω`-representation they agree with `ω` on
  `A ∩ Z_G`.

Cross-reference: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333
(literature ID `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`; PDF page =
printed page − 234). §III.1, Proposition III.1.1, printed p.263, restates the
criterion for an admissible representation with a unitary central character,
citing "[C, Théorème 4.4.6]". Its exponents (§I.3, p.243) are those of the
Jacquet module normalized by `δ_P^(-1/2)`, as in the Library.

## Translation to the Lean statement (derived)

The statement is the documented specialization of Theorem 4.4.6 to complex
representations of positive-rank `GL_n` over finite extensions of `Q_p`. The
source covers connected reductive groups over any non-archimedean local field.
The identifications below are standard computations for `GL_n`. They are
explained here and not stated in Lean.

- **Parabolics.** Take `P_∅` to be the upper triangular Borel subgroup, with the
  diagonal torus and the simple roots `α_j = e_j − e_(j+1)`. The standard
  parabolics `P_Θ` are then exactly the upper block parabolics `P_B` of the
  ordered block shapes `B` of `n`. `Θ = ∆` is `B = (n)`, and `Θ = ∅` is
  `B = (1, …, 1)`.
- **Split centre.** The centre of the block Levi `M_B` is the group of block
  scalars, and it is already split. So `A_Θ`, the centre of `M_Θ` and the image
  of `B.blockScalarLevi` coincide. Casselman's restriction from the centre of `M` to
  `A` is therefore the identity here.
- **Central characters and exponents.** `(V_N)_(χ,∞) ≠ 0` means that some
  `V_(χ,m)` is nonzero (p.21). That is the existence of a nonzero vector killed
  by one power `(π(a) − χ(a))^m` for all `a`, which is
  `IsGeneralizedEigencharacter` with a uniform power. For admissible `ρ` every
  such `χ` has open kernel: a nonzero vector of the generalized eigenspace is
  fixed by `A ∩ K_M` for some compact open `K_M ⊂ M`, and this forces
  `χ = 1` on `A ∩ K_M`. So the open-kernel field of `IsJacquetExponent`
  excludes nothing.
- **Normalization.** Casselman's `χ` is a character of the unnormalized Jacquet
  module. The exponent in Lean is a character of the normalized one, so it is
  `χ δ_(P_B)^(-1/2)` on block scalars. Casselman prints the minimal modulus
  `δ_∅`. On a block scalar, `Ad(a)` is trivial on the root spaces inside the
  blocks and multiplies the `(i, j)` block of `n_B` (`i < j`) by `a_i / a_j`.
  Hence `δ_∅(a) = δ_(P_B)(a) = ∏_(i<j) |a_i / a_j|^(n_i n_j)`, which is the
  published block modulus. So `|χ δ_∅^(-1/2)(a)|` is the norm of the Lean
  exponent at `a`.
- **Chamber.** For `α ∈ ∆ ∖ Θ` the simple root between blocks `j` and `j+1`
  takes the value `a_j / a_(j+1)` on a block scalar. So `A_Θ^-` is the set
  `|a_1| ≤ ⋯ ≤ |a_k|`, which is the `Monotone` hypothesis.
- **Removed directions.** `A_∅(O)` is the group of diagonal matrices with unit
  entries, and `A_∆` is the group of scalar matrices. A block scalar lies in
  `A_∅(O) A_∆` exactly when all `|a_i|` are equal. So
  `A_Θ^- ∖ A_∅(O) A_∆` is the `Monotone` set minus the elements with all
  `|a_i|` equal, which is the hypothesis `∃ i j, |a_i| ≠ |a_j|`. For
  `B = (n)` this set is empty and (b) says nothing, so (a) is not implied by
  (b) and is listed separately, as in the source.
- **`ω`-representations.** `Z_G` is the group of scalar matrices
  `GeneralLinear.scalar a`. The hypothesis on `ω` is Casselman's
  `ω`-representation, and (a) is his condition (a).

## Further derived choices

- **Nonzero carrier.** `Nontrivial V` is needed. For `V = 0`, any `ω` satisfies
  the `ω`-hypothesis. The zero representation satisfies
  `IsSquareIntegrableModCenter` with the trivial central character, so the left
  side holds while (a) fails for a non-unitary `ω`. Casselman's own definition
  (p.28) makes `|ω| = 1` part of square-integrability, so the source has no such
  case. For `V ≠ 0`, `ω` is determined by `ρ`, and it has open kernel because
  `ρ` is smooth.
- **All Haar measures.** `T.IsSquareIntegrable` requires square-integrability
  for every Borel Haar measure on `GL_n(F) ⧸ Z`, while Casselman assigns one
  Haar measure. Both sides of the Lean equivalence other than this predicate
  are measure-free. Casselman's proof uses the measure only through its
  invariance and the double-coset volumes of Prop. 1.5.2, which hold for any
  Haar measure. Conversely, a Borel Haar measure exists
  (`T.exists_isHaarMeasure_centralQuotient`). So the equivalence needs no Haar
  uniqueness.
- **Positive rank.** `0 < n`, as in the other `GL_n` statements of this family.

Illustration, not stated or proved in Lean: along the upper Borel subgroup of
`GL_2`, the trivial representation has the single exponent `|a_1 / a_2|^(-1/2)`.
Its norm exceeds one on the non-constant chamber `|a_1| < |a_2|`. The Steinberg
representation has the single exponent `|a_1 / a_2|^(1/2)`, which is below one
there.

## Not claimed

The definition proves nothing. In particular, none of the following is proved
or assumed:

- Casselman's criterion itself, or any part of its proof (Casselman's
  asymptotic expansion of coefficients, Theorem 4.3.4, Corollary 4.4.5);
- that the block scalars exhaust the centre of the block Levi, or that the
  explicit block modulus is the Haar modulus;
- finiteness of the set of exponents, or the decomposition of the Jacquet
  module into generalized eigenspaces;
- independence of the Haar measure in `IsSquareIntegrableModCenter`;
- the tempered exponent criterion, which is the separate statement
  `GLTemperedExponentCriterionStatement`.

## Lean dependencies

Direct imports are `Langlands.Representation.Classification.Tempered` (for
`T.IsSquareIntegrable`, Worker 23) and `Langlands.Representation.Exponents.Jacquet`
(for `T.IsJacquetExponent`, Worker 23). Through the latter come the published
block shapes `GeneralLinear.BlockShape` (`Langlands.Group.GL.Blocks`), the
normalized Jacquet module and the block modulus. `IsAdmissible`,
`GeneralLinear.scalar` and `T.normalizedAbs` are published Library
definitions.

This pair is authored for the pinned Lean 4.34.0 environment and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
