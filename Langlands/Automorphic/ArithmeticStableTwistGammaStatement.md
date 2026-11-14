# Arithmetic pair gamma factors after highly ramified twists

Author: Worker 389.

Module `Langlands.Automorphic.ArithmeticStableTwistGammaStatement` defines one proposition,
`Langlands.ClassField.Global.RelativeWeilGroup.ArithmeticStableTwistGammaStatement`
(universes `u`, `uV`, `uE`). It is a statement only: nothing is proved here, and no
definition is added or changed.

## Statement

Let `K` be a `p`-adic field, `eC` a common-closure reciprocity family, `ε` a common-closure
local-constant assignment with `hε : IsSystem K eC ε`, and `e` a rank-one reciprocity
candidate of `K` with `IsBaseReciprocity K e eC`. Let `ψ` be any nontrivial additive
character of `K`, `r`, `t` natural numbers, `ω`, `ω'` quasi-characters of `K^×`, and let
`X`, `X₀`, `Y`, `Y₀` be Weil–Deligne pair classes (`LocalPairClass`) such that

- `X` and `X₀` have representatives `B`, `B₀` of rank `r + 1` whose underlying Weil
  representations are continuous and whose determinant characters
  (`FiniteRepresentation.determinantCharacter`) both equal `ω ∘ e`
  (`Correspondence.weilCharacter K e ω`);
- `Y` and `Y₀` have representatives `B'`, `B₀'` of rank `t + 1`, continuous, with
  determinant characters both equal to `ω' ∘ e`.

The monodromy operators of the four representatives are arbitrary and unrelated, and no
Frobenius-semisimplicity is assumed.

Then there is a natural number `A` such that for every quasi-character `χ` of `K^×` whose
multiplicative conductor (`K.canonicalTopologicalData.multiplicativeConductor χ`) is at
least `A`, and every rational function `G`,

`IsArithmeticPairGammaFactor K eC ε hε ψ (twistClass (χ ∘ e) X₀) Y₀ G`

implies

`IsArithmeticPairGammaFactor K eC ε hε ψ (twistClass (χ ∘ e) X) Y G`.

Here `twistClass (χ ∘ e)` (`Weil/Representation/Twist.lean:42`, applied to
`Correspondence.weilCharacter K e χ`) twists the first class by the Weil character `χ ∘ e`;
only the first factor is twisted. `IsArithmeticPairGammaFactor`
(`Correspondence/SupercuspidalGammaCompatibility.lean:27`) says that for some `c` and `m`
the pair `c q^(-ms)` is the arithmetic epsilon factor of the pair for the system `ε` and
`ψ` (`IsArithmeticPairEpsilonFactor`, `Correspondence/ArithmeticFactors.lean:96`), and
`G = c X^m · L((X ⊗ Y)^∨)(q⁻¹/X) / L(X ⊗ Y)(X)` is that monomial times the reflected
L-ratio of the tensor class. So the conclusion says
`γ(s, (X₀ ⊗ χ) ⊗ Y₀, ψ) = γ(s, (X ⊗ χ) ⊗ Y, ψ)` for every such `χ`, as one implication
between the existing relations. Since the hypotheses are symmetric in `(X, Y)` and
`(X₀, Y₀)`, the converse implication follows from the same proposition with the roles
exchanged (with a possibly different bound).

The bound `A` may depend on all data except `χ` and `G`.

## Provenance (derived)

Sources:

- G. Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of Math.
  123 (1986), 145–203 (`henniart-1986-cyclic`, SHA-256
  `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`), §4.2, Lemma, parts
  (1) and (2) and the first paragraph of its proof, printed p. 158 (PDF p. 15).
- P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
  d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981), 89–118
  (`deligne-henniart-1981-variation`, SHA-256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`), Théorème 4.6,
  printed p. 110 (PDF p. 22).

Henniart's Lemma 4.2 says: for `σ` an `n`-dimensional representation of the Weil–Deligne
group and every character `χ` of `F^×` of sufficiently large exponent,
(1) `L(χσ) = L(χ⁻¹σ^∨) = 1` and (2) `ε(χσ) = ε(χ)^(n-1) ε(χ · Det σ)`. Its proof derives
both from Deligne–Henniart Theorem 4.6: for `χ` of sufficiently large conductor,
`ε(χσ) = ε(χ)^n Det σ(c_χ)` with `c_χ ∈ F^×` depending only on `χ`, applied to `σ` and to
the sum of `Det σ` and `n - 1` trivial characters. In particular the twisted epsilon factor
and the L-factors of `χσ` depend only on `n` and `Det σ` once `χ` is deep enough.

The present proposition applies this to `σ = B ⊗ B'` and `σ₀ = B₀ ⊗ B₀'`. Both have dimension
`(r + 1)(t + 1)`, and `Det(B ⊗ B') = (Det B)^(t+1) (Det B')^(r+1)
= (ω^(t+1) ω'^(r+1)) ∘ e = Det(B₀ ⊗ B₀')`. Since `(B ⊗ χ∘e) ⊗ B' = χσ` and
`(B₀ ⊗ χ∘e) ⊗ B₀' = χσ₀`, Lemma 4.2 (1)–(2) give equal L-factors (all `1`) and equal
epsilon factors, hence equal gamma factors. The statement is the resulting comparison,
written with the Library's relations (`IsArithmeticPairGammaFactor`, `twistClass`,
`weilCharacter`, conductor of `χ`) and as an implication between gamma certificates; this
is why it is recorded as derived content and not as a verbatim theorem.

Extension to arbitrary monodromy. Henniart 1986 §2.2–2.3 (printed p. 150) works with
semisimple representations of the Weil–Deligne group. The Lean statement allows any
continuous Weil–Deligne representatives. The comparison still holds:

- a continuous complex representation of the Weil group has finite inertia image, so for
  `χ` of conductor larger than every conductor occurring in `B ⊗ B'` and `B₀ ⊗ B₀'`, the
  inertia invariants of the twisted tensor products and of their duals are zero; hence their
  arithmetic L-factors are `1` and the monodromy correction of the Weil–Deligne epsilon factor
  is trivial, whatever the monodromy;
- the system `ε` is defined on the exact Grothendieck group of continuous Weil
  representations, so the remaining epsilon factor depends only on the exact Grothendieck
  class of the underlying Weil representation, where Theorem 4.6 applies (its virtual,
  degree-zero form is the Library's proved
  `LocalFactor.NonabelianSystem.DeligneHenniart.VirtualStabilityStatement`, stated for every
  assignment satisfying `IsSystem`).

Design choices and why they are needed for truth:

- Continuity of all four representatives is assumed because the arithmetic pair epsilon
  factor is only defined through continuous base restrictions.
- Equal ranks and equal determinant characters are what make the virtual difference
  `σ - σ₀` have degree zero and trivial determinant, which is the hypothesis under which
  Theorem 4.6 makes the twisted epsilon factors agree.
- `ψ` is arbitrary and the same on both sides, so no conductor condition on `ψ` is needed.

## Intended use

Together with a Rankin–Selberg stability statement for principal series and the
Jacquet–Shalika stability theorem, this reduces
`StableTwistPairGammaMatchStatement` (Henniart 1986, Lemma 4.2 and §4.3) to the case of
semisimple diagonal Weil–Deligne classes matching principal series representations.
