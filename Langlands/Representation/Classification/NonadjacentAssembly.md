# Core of the BZ77 Theorem 4.2 argument

Author: Worker 745. Helper module of the proof of Ze80 Proposition 1.11(a),
first conjunct (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`). It is imported
by `NonadjacentSpecialization` and, through it, by the final module
`TwoSupercuspidalNonadjacentIrreducibilityProof`.

## What is proved

`irreducible_of_pieces` proves the following for a smooth complex
representation `π` of `GL_(N+1)`, a nontrivial unitary additive character
`ψ`, and these hypotheses:

1. `hE`: the published proposition
   `Derivative.GeneralLinearDerivativeExactnessStatement` (exactness of the
   derivative functors).
2. `hPL`: the published proposition `Derivative.MirabolicDerivativeDetection`
   (detection by derivatives, BZ77 §3.5).
3. `hHP`: the published proposition
   `Derivative.MirabolicHighestDerivativePairingStatement` (BZ77
   Proposition 3.8).
4. The top derivative of `π` (order `N+1`) has `finrank ℂ` equal to `1`.
5. `PiecesWithoutForms ψ N π`: at every order `0 < d < N+1`, the derivatives
   of `π` and of `ν π~` have actual filtrations whose graded pieces are zero or
   irreducible, and no pair of graded pieces carries a nonzero invariant
   bilinear form.

Under these hypotheses `π` is irreducible.

Hypotheses 1–3 are proposition definitions, taken here as arguments so that
this module stays independent of their proofs. The final theorem supplies them
with their published proofs (`Derivative.generalLinearDerivativeExactness`,
`Mirabolic.derivativeDetection`, `mirabolicHighestDerivativePairing`); see
`NonadjacentLeibnizPieces.md`.

## Source

This is the argument of BZ77 §§4.7–4.8 (Bernstein and Zelevinsky 1977,
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
printed p.455, PDF p.16), restructured as follows.

- BZ77 picks a degenerate Jordan–Hölder factor `ω` and embeds it as a
  submodule after permuting the factors (via 4.1). The Lean proof needs
  neither finite length nor the permutation. A proper nonzero invariant
  subspace `S` gives the exact sequence `0 → S → π → π/S → 0`. Exactness of the
  top derivative and `finrank = 1` make the top derivative vanish on `S` or on
  `π/S`. Call that constituent `X`. It is a subrepresentation or a quotient of
  `π`.
- BZ77 then takes an irreducible submodule `σ` of the highest derivative of
  `ω` and compares supports. The Lean proof does not choose `σ`. It bounds the
  length of the space of invariant forms on the two highest derivatives by
  the graded pieces of the two filtrations
  (`length_eq_zero_of_isSubOrQuotient`). The forms vanish there, which
  contradicts the nonzero form from BZ77 3.8.

## Declarations

Namespace `Langlands.Classification.NonadjacentAssembly`.

- `isSubOrQuotient_map`: a functor satisfying the published
  `Mirabolic.MapsShortExactIntertwiners` sends an injective intertwiner to an
  injective one and a surjective intertwiner to a surjective one. The proof
  completes the map to a short exact sequence using the published cokernel and
  kernel constructions of `SmoothRep`.
- `formsCast`: transport of a form along a pointwise equality of covariance
  characters.
- `dualTwistRep π`: `ν π~`, the published `contragredient` twisted by
  `T.determinantPowerCharacter (N+1) 1`.
- `restrictedDerivative ψ N d hd`: `generalLinearRestriction T N ⋙
  mirabolicDerivativeOfOrder T ψ N d hd`. By
  `generalLinearDerivative_eq_restriction_comp` (module
  `TwoSupercuspidalDerivativeBridge`) this equals the published
  `generalLinearDerivative T ψ (N+1) d`. `restrictedDerivative_exact` derives
  its exactness from `hE` in this way.
- `PiecesWithoutForms ψ N π`: hypothesis 5 above, with covariance `1`.
- `false_of_constituent`: a nontrivial `X` that is a subrepresentation or a
  quotient of `π`, with zero top derivative, and with `ν X~` correspondingly a
  subrepresentation or a quotient of `ν π~`, contradicts the hypotheses. The
  proof:
  1. `hPL` and the published `level_eq_iff` give `0 < d = level(X|P) ≤ N+1`.
     The `d`-th derivative of `X|P` is nonzero and all higher ones vanish.
     Since the top derivative vanishes, `d < N+1`.
  2. The published `smoothDualEvaluation` of `X` with the twist `ν`, pulled
     back to `P` by `comapGroup`, is a form on `X|P × (ν X~)|P` with covariance
     `|det|`. It is left-separating by the published
     `smoothDualEvaluation_separatingLeft`, using the cofinal compact open
     subgroups of `GL_(N+1)`. This is the step in BZ77 §4.8(b), printed
     p.455: "the natural 1-pairing of `π` and `π~` induces a `ν⁻¹`-pairing"
     of `π` and `ν π~`, whose restriction to `P` is a `Δ`-pairing. The two
     conventions are inverse to each other. BZ77 §3.6 (printed p.452) defines
     a `χ`-pairing by `χ(g) B(π₁(g)v, π₂(g)w) = B(v, w)`, and §4.2 (printed
     p.454) gives the modulus of `P` as `Δ_P = ν⁻¹|_P = |det|⁻¹`. The Library's
     `InvariantBilinear.forms ρ σ χ` instead asks for
     `B(ρ(g)v, σ(g)w) = χ(g) B(v, w)`. So a BZ77 `Δ_P`-pairing is a Library
     form with covariance `Δ_P⁻¹ = |det|`. That is the covariance of `β`, and
     it is the covariance `fun g => |det g|` that the published 3.8 statement
     `MirabolicHighestDerivativePairingStatement` takes as input. The Lean
     proof writes `ν` as `determinantPowerCharacter (N+1) 1`, and `Real.rpow_one`
     identifies `ν ∘ φ` with `determinantNorm (N+1)`.
  3. `hHP` gives a left-nondegenerate form `γ` on the `d`-th derivatives of
     `X` and of `ν X~` with covariance `1`. It is nonzero because the `d`-th
     derivative of `X` is nontrivial.
  4. By exactness (`isSubOrQuotient_map`), these derivatives are a
     subrepresentation or a quotient of the `d`-th derivatives of `π` and of
     `ν π~`. `length_eq_zero_of_isSubOrQuotient` (my published module
     `Filtration.InvariantBilinearSubquotientBounds`) and the filtrations
     from hypothesis 5 make the space of such forms zero. Hence `γ = 0`, a
     contradiction.
- `irreducible_of_pieces`: the main result. `π` is nontrivial because its top
  derivative is. For a proper nonzero `S`, exactness gives
  `0 → D(S) → D(π) → D(π/S) → 0` for the top derivative `D`. If `D(S) = 0`,
  take `X = S`. Then `ν X~` is a quotient of `ν π~`, by the published
  `contragredientMap_surjective_of_injective_of_compact_cofinal`. Otherwise
  `D(S)` contains a nonzero vector, which spans the one-dimensional `D(π)`.
  So `D(π/S) = 0`, and we take `X = π/S`. Then `ν X~` is a subrepresentation
  of `ν π~`, by the published `contragredientMap_injective_of_surjective`.
  Both cases end in `false_of_constituent`.

## Universes and parameters

`F : PadicField.{uF} p` and `T` are explicit, with `T.topology` installed. The
representation universe `u` is used for `π`. The published statements are
instantiated as `GeneralLinearDerivativeExactnessStatement.{uF, u}`,
`MirabolicDerivativeDetection.{uF, u}` and
`MirabolicHighestDerivativePairingStatement.{uF, u, u}`. The final theorem
uses `u = max uF uV`, the carrier universe of `ρ × ρ'`.

## Provenance and dependency audit

All proofs here are original to this module; no code is adapted from other
Library proofs. Direct imports: `Filtration.InvariantBilinearSubquotientBounds`
(my published module), `Classification.TwoSupercuspidalDerivativeBridge`, the
statement modules `Derivative.GeneralLinearDerivativeExactnessStatement`,
`Derivative.MirabolicHighestDerivativePairingStatement` and
`Derivative.MirabolicDerivativeDetectionStatement`,
`Filtration.SmoothDualEvaluation`, `Category.Subquotients`,
`Category.Contragredient`, `Classification.SupercuspidalTwist` and
`Smooth.Contragredient.ExactProof`. These are derivative definitions and
statements, smooth duality and general representation theory. No segment,
socle, head, multisegment, classification, square-integrability or
product-irreducibility result is imported or used.
