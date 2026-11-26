# The uniform center ideal from the Levi transfer and the Haar factor

Module `Langlands.Global.AdelicIntertwiningCenterIdealReductionStatement` contains one `Prop`-valued
definition, `Langlands.Global.IntertwiningUniformCenterIdealReductionStatement`. It is the
implication

`LeviRestrictionCenterTransferStatement → IntertwiningStabilizerModulusStatement →
IntertwiningUniformCenterIdealStatement`

between three published propositions, all at the same universe `u`:

- `LeviRestrictionCenterTransferStatement` (module `AdelicLeviCenterTransferStatement`): for every
  central `z` there is one element `y` of the enveloping algebra of `M'(F_∞)` acting as `z` on the
  `δ^{-1/2}`-normalized restrictions to `M'(F_∞)` of functions left invariant under `V(F_∞)` and,
  after transport by `w`, of functions left invariant under `U(F_∞)`;
- `IntertwiningStabilizerModulusStatement` (module `AdelicIntertwiningStabilizerModulusStatement`):
  the Haar factor of a target Levi conjugation in the intertwining integral is
  `δ_Q^{1/2} δ_P(w⁻¹ · w)^{-1/2}`;
- `IntertwiningUniformCenterIdealStatement` (module `AdelicIntertwiningAutomorphyStatement`): there
  are a threshold `R₀` and one ideal of finite codimension in the center of the complex enveloping
  algebra annihilating every plot-smooth infinite slice of `M(w, λ)φ` for every `R₀`-regular `λ`.

The module `AdelicIntertwiningCenterIdealReduction` proves the implication
(`intertwiningUniformCenterIdealReduction`).

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024) (`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): (6.5) and the
  sentence after it, p. 201, and the proof of the Lemma in §8.2, p. 222. The proof takes a
  finite-codimensional ideal of `𝔷^M` annihilating the normalized Levi restrictions of `φ`, carries
  it by (6.5) to the restrictions of `M(w, λ)φ`, and obtains "a finite-codimensional ideal of `𝔷`
  (independent of `λ`) that annihilates `M(w, λ)φ`".

## Provenance

The implication is internal to the Library. Its premises are the Lie-theoretic input of the
source argument, the Harish-Chandra transfer to the Levi subgroup with its independence of the
parabolic, and the modulus identity behind (6.5). The proof of the implication supplies the
analytic part of the argument. The conclusion is the published target statement.
