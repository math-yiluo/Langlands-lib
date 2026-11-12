# The adelic modulus `δ_P` as an idele norm and as a modular character

Author: Worker 3659.

`Langlands.Global.AdelicGroupPoints.AdelicParabolicModulusStatement` is a
proposition definition. It asserts no proof and is a target for a
separate proof task.

## Statement

Let `F` be a number field in universe `u`, and let `G` be a connected
reductive group scheme over `Spec F` (`IsConnectedReductive G`). Let
`χ : 𝔾_m ⟶ G` be a cocharacter. Let `iP : P ⟶ G` and `iU : U ⟶ G`
represent the published dynamic subgroup functors `Dynamic.parabolic χ`
and `Dynamic.unipotent χ`, that is, `P = P_G(χ)` and `U = U_G(χ)`. Let
`c : Lie.FiniteCoordinates U d` be any finite coordinates on `Lie U`.
Then:

1. For every `p ∈ P(𝔸_F)`,
   `parabolicModulus F hP hU p = characterNorm F P (Dynamic.adjointDeterminantCharacter hP hU c).toMul p`
   in `ℝ≥0ˣ`.
2. For every `p ∈ P(𝔸_F)`,
   `Measure.modularCharacter p = parabolicModulus F hP hU p` in `ℝ≥0`.

The objects in the statement are these:

- `parabolicModulus F hP hU` is `δ_P` from `AdelicParabolicModulus.lean`.
  It is the Haar modulus of conjugation by `p` on the closed subgroup
  `U(𝔸_F)` of `G(𝔸_F)`: `μ(p E p⁻¹) = δ_P(p) μ(E)`.
- `Dynamic.adjointDeterminantCharacter hP hU c` is the published rational
  character `det(Ad | Lie U)` of `P`.
- `characterNorm` is the published normalized idele norm of an algebraic
  character. Complex places use the squared absolute value.
- `Measure.modularCharacter` is Mathlib's modular character of the
  locally compact group `P(𝔸_F)`. Its value at `p` is the factor `Δ(p)`
  in `map (· * p) μ = Δ(p) • μ` for a left Haar measure `μ`. This is the
  convention of Getz–Hahn (3.6)–(3.8).

The local `haveI` lines only install instances that the published lemmas
prove for these data. `G` is affine and smooth, so it is locally of finite
type. `isAffine_parabolic`, `locallyOfFiniteType_parabolic` and
`isAffine_unipotent` come from `AdelicParabolicModulus.lean`; they make
`P(𝔸_F)` locally compact and `Lie U` defined. No hypothesis is added.

The statement is not vacuous. The published
`Langlands.GroupScheme.dynamicAdjointDeterminantExistence` gives
coordinates `c` for every connected reductive `G` and every `χ`. By the
published `Langlands.GroupScheme.Dynamic.adjointDeterminantModelIndependence`,
the character does not depend on `c`.

## Sources and conventions

- Mœglin–Waldspurger I.1.13, printed p. 18, use the modulus
  `m ↦ m^{2ρ_P}` of a standard parabolic on `M(𝔸)`. They write
  `m^{-2ρ_P}` for its inverse in the integration formula. On `M(𝔸)`,
  conjunct 1 says that this modulus is the idele norm of
  `det(Ad | Lie U)`, the character `2ρ_P`.
- Getz–Hahn (8.1), printed p. 213, define the local
  `δ_P(p) = |det(Ad(p) : Lie P → Lie P)|`. Proposition 3.6.1, printed
  p. 88, identifies this with the modular quasi-character of `P(F_v)`.
  Equations (3.11)–(3.13), printed pp. 89–90, pass to adelic points.
  Since `Z_G(χ)` is reductive, `det(Ad | Lie Z_G(χ))` is trivial, and the
  determinant on `Lie P` equals the determinant on `Lie U`. This is the
  content of conjunct 2.

## Proof route (not part of the statement)

- Conjunct 2 can start from the published, proved ambient comparison
  `AdelicModularCharacterAdjointDeterminantStatement`. It follows from
  `adelicModularCharacterAdjointDeterminantStatement_of_local` and
  `localModularCharacterAdjointDeterminant`. Applied to the smooth
  connected affine group `P`, it gives
  `Δ_{P(𝔸)} = |Lie.adjointDeterminantCharacter P|`. What remains is the
  algebraic identity `det(Ad | Lie P) = det(Ad | Lie U)` on `P`, together
  with conjunct 1.
- For conjunct 1, the published non-archimedean
  `Aubert.General.RationalPointFamily.dynamicUnipotentHaarDeterminant`
  treats Levi points at one place. The adelic statement needs every
  place, every point of `P(𝔸_F)`, and the restricted product structure of
  `U(𝔸_F)`.

## Sources

- Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
  (`moeglin-waldspurger-1995-spectral-decomposition`), chapter file
  `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.13, printed
  p. 18 (PDF p. 18).
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024)
  (`getz-hahn-2024-automorphic-representations`):
  - (3.6)–(3.8), printed p. 82 (PDF p. 98);
  - Proposition 3.6.1, printed p. 88 (PDF p. 104);
  - (3.11)–(3.13), printed pp. 89–90 (PDF pp. 105–106);
  - (8.1), printed p. 213 (PDF p. 226).
