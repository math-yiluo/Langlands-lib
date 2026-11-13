# Stable pair gamma comparison under highly ramified twists

Module `Langlands.Automorphic.StableTwistGammaMatchStatement` defines one proposition,
`Langlands.ClassField.Global.RelativeWeilGroup.StableTwistPairGammaMatchStatement`
(universes `u`, `uV`, `uE`). It is a statement only; nothing is proved here.

## Statement

Let `K` be a `p`-adic field, `eC` a common-closure reciprocity family, `ε` a common-closure
local-constant assignment with `hε : IsSystem K eC ε`, and `e` a rank-one reciprocity
candidate of `K` with `IsBaseReciprocity K e eC` (the bottom component of `eC` agrees with `e`).
Let `ψ` be any nontrivial additive character of `K`, and let

- `π` (rank `r + 1`) and `π'` (rank `t + 1`) be classes of irreducible admissible smooth
  representations of `GL_(r+1)(K)`, `GL_(t+1)(K)`, each with a representative that is generic
  for `ψ` (`Whittaker.IsGeneric`, which includes irreducibility and admissibility);
- `ω`, `ω'` be quasi-characters of `K^×` such that every scalar matrix `a` acts on (a
  representative of) `π`, `π'` by `ω(a)`, `ω'(a)` (`CentralActsBy`);
- `X`, `Y` be Weil–Deligne pair classes of the local Weil group with representatives `B`, `B'`
  of ranks `r + 1`, `t + 1` whose underlying Weil representations are continuous and whose
  determinant characters are `ω ∘ e` and `ω' ∘ e` (`weilCharacter K e ω`). The monodromy of
  `B`, `B'` is arbitrary.

Then there is a natural number `A` such that for every quasi-character `χ` of `K^×` with
multiplicative conductor at least `A`, and every class `πχ` that is the twist of `π` by
`χ ∘ det` (`IsCharacterTwist K χ π πχ`),

`IsPairGammaMatch K eC ε hε ψ πχ π' (twistClass (χ ∘ e) X) Y`,

that is, a self-dual Haar measure for `ψ` exists, and for each such measure one rational
function is both the representation-side gamma factor `γ(s, πχ × π', ψ)` and the arithmetic
gamma factor `γ(s, (X ⊗ χ∘e) ⊗ Y, ψ)` for the system `ε`.

Only the first factor is twisted. The bound `A` may depend on all data except `χ` and `πχ`.

## Provenance (derived)

Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of Math. 123
(1986), Lemma 4.2 (printed p. 158, PDF p. 15), together with its use in §4.3. For `σ` of
dimension `n`, `π` of `GL_m`, `π'` of `GL_m'` and `χ` of sufficiently large exponent, Lemma 4.2
gives `L(χσ) = L(χ⁻¹σ^∨) = 1`, `ε(χσ) = ε(χ)^(n-1) ε(χ · Det σ)` (from Deligne–Henniart 1981,
Theorem 4.6) and `L(χπ × π') = L(χ⁻¹π^∨ × π'^∨) = 1`,
`ε(χπ × π') = ε(χ)^(mm'-1) ε(χ ω_π^(m') ω_(π')^m)` (from Jacquet–Shalika stability and the
principal-series computation of §2.6). Both sides therefore depend only on the dimensions and
on the central characters or determinants. The present proposition is the resulting
comparison for a pair `X ⊗ Y` on the arithmetic side and `π × π'` on the representation side:
under the matching of central characters with determinants through `e`, the stable formulas
coincide, so the gamma factors coincide. It is stated with the Library's vocabulary
(`IsPairGammaMatch`, `IsCharacterTwist`, `twistClass`, `weilCharacter`), which is one reason it
is recorded as derived content rather than a verbatim theorem.

The second, mathematical, extension concerns the domain of the arithmetic side. Henniart 1986
§2.2–2.3 (printed p. 150, PDF p. 7) works with semisimple representations of the Weil–Deligne
group `W'_E`, and Lemma 4.2 uses that domain. The Lean statement instead allows any continuous
Weil–Deligne representatives `B`, `B'` (arbitrary monodromy, no Frobenius-semisimplicity
condition). The stable comparison still holds for them:

- a continuous complex representation of the Weil group has finite inertia image, so for `χ`
  of conductor larger than every conductor occurring in `B ⊗ B'` the inertia invariants of
  `(B ⊗ χ∘e) ⊗ B'` are zero; hence the arithmetic L-factors of the twisted pair and of its dual
  are `1`, whatever the monodromy and whether or not Frobenius acts semisimply;
- the system `ε` is defined on the exact Grothendieck group (`ExactGrothendieckGroup`), so the
  arithmetic epsilon factor depends only on the exact Grothendieck class of the underlying Weil
  representation, which equals the class of its semisimplification; there the Deligne–Henniart
  formula applies, and the determinant is also unchanged by semisimplification.

So the arithmetic gamma factor of the twisted pair agrees with that of its Frobenius
semisimplification, to which Henniart's lemma applies.

Design choices and why they are needed for truth:

- Continuity of `B`, `B'` is assumed because the arithmetic pair epsilon factor
  (`IsArithmeticPairEpsilonFactor`) is only defined through continuous base restrictions;
  for a non-continuous class the arithmetic side does not exist.
- Genericity of `π`, `π'` is assumed because the representation-side factors
  (`IsAutomorphicPairGammaFactor`) are Rankin–Selberg factors of generic representations.
- `ψ` is arbitrary. Write `m = r + 1`, `n = t + 1`. The first factor of the compared pair is the
  twist: `πχ` has central character `ωχ^m`, and `(B ⊗ χ∘e)` has determinant `(ωχ^m)∘e`.
  Changing `ψ` to `x ↦ ψ(ax)` therefore multiplies both gamma factors by the same factor
  `χ(a)^(mn) ω(a)^n ω'(a)^m |a|^(mn(s - 1/2))` (that is,
  `ω_(πχ)(a)^n ω'(a)^m |a|^(mn(s - 1/2))`, with self-dual measures on both sides). For
  `m = n = 1` the character part `χ(a)ω(a)ω'(a)` is the factor in the rank-one scaling law
  `abelianEpsilonExpression_scale` of `Langlands/LocalFactor/Abelian/Scaling.lean` (stated there
  for a fixed Haar measure, hence with a different power of `|a|`). So no conductor condition on
  `ψ` is imposed.

## Intended use

At the finitely many bad places, Henniart 2000 §2 (Théorème 2.3) isolates the gamma factor at
one place by twisting with a global character that is highly ramified at the other bad
places. This statement supplies the local equality at those other places (the
`RamifiedGammaStability` input of the Library adapter
`Langlands.Global.FunctionalEquationComparison.relativeGammaComparison`).
