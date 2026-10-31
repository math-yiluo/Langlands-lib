# Vanishing of bi-equivariant distributions on character-incompatible Bruhat cells: proof

Authors: Worker 634 and Worker 1025. Worker 634 wrote the complete private proof
`BruhatCellVanishingCore.vanishing_of_factorization` of the identical private design
statement, shared in parent draft revision 8 of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`
(`Langlands/Representation/Whittaker/BruhatCellVanishingCore.lean`, SHA256
`a3d47157fbabce95e162ee10c4075fdf4d79d32bb2302ec373e851783c0b1285`). Worker 1025
ported it into this module. The private helper took a proof of the private factorization
design statement as a premise and was then applied to the private factorization
preparation. Here there is a single theorem, renamed
`Langlands.Whittaker.bruhatCellVanishing`, which targets the published statement and
applies the published factorization theorem `bruhatCellFactorization` directly in its
proof, so it has no factorization premise. One unused local abbreviation for the cell
was dropped; the remaining tactic steps are Worker 634's. Worker 1025 also wrote the
docstrings and this Markdown.

This module proves `Langlands.Whittaker.bruhatCellVanishing.{uF}`, whose type is exactly
the published proposition `Langlands.Whittaker.BruhatCellVanishingStatement.{uF}` of
`Langlands.Representation.Whittaker.BruhatCellVanishingStatement`. The statement module
and everything it imports are used unchanged. Besides the statement module, the proof
imports only the published modules

- `Langlands.Representation.Whittaker.BruhatCellFactorizationProof`, for
  `Langlands.Whittaker.bruhatCellFactorization` (the proof of
  `BruhatCellFactorizationStatement`);
- `Langlands.Representation.Whittaker.BruhatHaarMeasureProof`, for
  `Langlands.Whittaker.bruhatHaarMeasure` (the proof of `BruhatHaarMeasureStatement`);
- `Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof`, for
  `Langlands.Whittaker.bruhatOrbitalIntegration` (the proof of
  `BruhatOrbitalIntegrationStatement`). This module is also imported by
  `BruhatCellFactorizationProof`; it is listed explicitly because the proof calls its
  theorem.

It imports no private or design module. It adds no hypothesis, axiom or proof hole. The
only axioms of the theorem are `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Everything the statement quantifies is kept: the universe `uF`, every prime `p`, every
p-adic field `F : PadicField.{uF} p` with its canonical normed field structure
`F.canonicalNormedField` and the topologies it induces, every `n : ℕ` (so every rank
`n + 1`, rank one included), every bundled (continuous, nontrivial) unitary additive
character `ψ : UnitaryAdditiveCharacter F.Carrier` and every permutation `w` of
`Fin (n + 1)`. The only premise on the cell is `¬ (compatibleTorus ψ n w).Nonempty`. The
conclusion is the statement's: every algebraic distribution
`D : Distribution (UpperBruhatCell (n + 1) F.Carrier w)` with
`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D` (two positive character
factors) is zero.

`D` is an arbitrary complex-linear functional on the test functions of the actual cell
subtype. No continuity of `D` and no measure, support, factorization, countability,
cell-stability or auxiliary invariance hypothesis is assumed. The Haar measures, the
orbital integral and the torus distribution are all obtained inside the proof from
published theorems.

## Notation

Write `K = F.Carrier`, `U = upperUnipotent (n + 1) K`,
`P = U_w⁺ = permutationUnipotentPlus (n + 1) K w`, `H = Fin (n + 1) → Kˣ`,
`M = U × (H × U)`, `C = UpperBruhatCell (n + 1) K w`, `π = upperBruhatTorusMap (n + 1) w`
and `χ = standardCharacterContinuous ψ n`. `U` and `P` carry their Borel σ-algebras
(`borel U`, `borel P`), and `U` the instance `BorelSpace U` (proved by `rfl`). These are
exactly the local definitions of the published `BruhatCellFactorizationStatement`.

## The proof

The proof introduces `p`, `hp`, `F`, installs `F.canonicalNormedField`, and introduces
`n`, `ψ`, `w`, the emptiness premise `hempty`, `D` and its bi-equivariance `hD`.

1. **Haar measure on `U`.** The first component of the published
   `bruhatHaarMeasure p hp F n` gives a measure `μ` on `U` with `μ.IsHaarMeasure`. Its
   second component, applied to `μ`, gives `SigmaFinite μ` and `μ.IsMulRightInvariant`;
   the transpose clause is discarded. These are installed as instances. `SigmaFinite`
   supplies, through Mathlib's instance, the `SFinite μ` required by the factorization
   statement.
2. **Haar measure on `P`.** The third component of `bruhatHaarMeasure p hp F n` at `w`
   gives a measure `ν` on `P` with `ν.IsHaarMeasure` and, for it, `ν.IsMulRightInvariant`
   (its σ-finiteness is not used). Both are installed as instances.
3. **Orbital integral.** The published `bruhatOrbitalIntegration p hp F n w ν` gives a
   complex-linear map `I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C` with the evaluation
   formula
   `hI : ∀ α m, I α (π m) = bruhatFiberAverage (n + 1) K w ν α m`
   and surjectivity `hsurj`. Its support clause and its uniqueness are not used.
4. **Factorization.** The published
   `bruhatCellFactorization p hp F n ψ w μ ν I hI D hD` gives a torus distribution
   `τ : Distribution H` with
   `hsupp : τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)` and
   `hτ : Distribution.characterAverageDual χ μ τ = D.comp I`.
   Its uniqueness is not used.
5. **The torus distribution vanishes.** `τ = 0`: for every test function `f` on `H`,
   `Distribution.mem_supportedOn_iff` turns `hsupp` into the implication
   `(∀ d ∈ compatibleTorus ψ n w, f d = 0) → τ f = 0`. Its hypothesis holds vacuously:
   a point `d` of the compatible torus would make it nonempty, contradicting `hempty`.
   So `τ f = 0`, which is the value of the zero distribution at `f`.
6. **The pulled-back distribution vanishes.** `D.comp I = 0`: rewrite `D.comp I` as
   `characterAverageDual χ μ τ` by `hτ`, then `τ` as `0`, and use `map_zero`, since the
   published `characterAverageDual χ μ` is complex-linear.
7. **Conclusion.** For a test function `f` on `C`, surjectivity gives `α` with
   `I α = f`. Then `D f = D (I α) = (D.comp I) α = 0 α = 0`. By extensionality
   `D = 0`.

## Remarks on the route

- No distribution is commuted with an integral. `D` and `τ` are applied only to single
  test functions, and only linearity (`map_zero`) of `characterAverageDual` is used.
- The argument uses only the definition of `Distribution.supportedOn` on the empty
  compatible torus; no analysis takes place in this module. All analytic content is in
  the published Haar, orbital-integration and factorization theorems.
- Rank one is not treated separately. There the premise never holds, since the
  published `compatibleTorus_rankOne` makes the compatible torus all of `H`, so the same
  proof applies vacuously; the proof does not use this fact.

## Provenance

The proof route is internal. It realizes the steps outlined in the statement's Markdown
("Intended later proof"), which make explicit the empty case left implicit in the proof
of Proposition 1.8 on printed p.178 of J. A. Shalika, *The multiplicity one theorem for
GL_n*, Ann. of Math. (2) **100** (1974), 171–193 (registered
`shalika-1974-multiplicity-one`). That proof combines the surjective orbital integration
of Lemma 1.10 and (1.11) (printed p.176) with the factorization `T(f_α) = τ(β_α)` of
Proposition 1.12 and the support statement of Proposition 1.13 (printed p.177), here the
published Haar, orbital-integration and factorization theorems. If `H_χ` is empty, `τ`
is zero, and so is `T`. The statement's companion Markdown explains the derived scope and
conventions.

## Scope

This proves only `BruhatCellVanishingStatement`, the empty-compatible-torus case. It
does not prove the complementary nonempty case (the separate published
`Langlands.Whittaker.bruhatCellInvariance`), restriction of an ambient distribution to a
cell, global transpose invariance of distributions on `GL_{n+1}` (Shalika's
Theorem 1.6), the finite-filtration assembly or Whittaker multiplicity one; those are
separate results.
