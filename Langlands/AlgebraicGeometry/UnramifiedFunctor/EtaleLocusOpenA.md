# Openness near a point over a non-nilpotent prime

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusOpenA`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusStep`.

## `exists_open_van`

With `I`, `Lvs` and `ξ` as in `EtaleLocusCaseA` and a level `c`, there is an
open set `V` of `Spec (R'/𝔍)` such that for every `w` with `I ⊆ P_w`:
`w ∈ V ↔ VanN c w`.

Proof. Let `B_c = R'/(𝔍 + I^{c+1})`. Restricting `ξ` to `Spec B_c` gives an
element over `Spec B_c` with structure morphism through `Spec (R'/I^{c+1})`.
Let `Φ : Spec B_c ⟶ X_c` be the corresponding morphism to the scheme of level
`c`. Write `𝔍 = (G)` with `G` finite (`R'` is noetherian). Then
`S = {x | structMap(x)(g) = 0 for all g ∈ G}` is open
(`isOpen_structMap_eq_zero`), and so is `Φ⁻¹(S)`. Since `R'/𝔍 → B_c` is
surjective, `Spec B_c → Spec (R'/𝔍)` is an embedding
(`PrimeSpectrum.comap_isInducing_of_surjective`). So `Φ⁻¹(S)` is the preimage
of an open `V`.

For `w` with `I ⊆ P_w`, let `κ : B_c → L_c(w)` be induced by `R' → O_w`. Then:

- `Spec κ ≫ Φ` is the point `mor` of `nDatum c w`. The restriction of the
  element of `Φ` along `Spec κ` is `ζ`, so `left_of_map_eq` applies.
- `w̄ = Spec κ(closed point)` lies over `w` (`comap_eq`).

Hence `w ∈ V ↔ w̄ ∈ Φ⁻¹(S) ↔ pt ∈ S ↔ VanN c w`. The last step holds because a
ring map kills `𝔍` exactly when it kills `G`.

## `exists_open_of_not_le_nilradical` (Murre's case (a))

Let:

- `R` be noetherian and `R'` étale over `R`;
- `F` satisfy strong (F5);
- the base change of `F` to every `Spec (R/I)` with `I ≠ 0` satisfy
  `UnramifiedRepresentable`;
- `y` be a point at which `ξ` is infinitesimally étale, whose prime
  `𝔭 = y ∩ R` is not contained in the nilradical.

Then there is an open `V ∋ y` such that `ξ` is infinitesimally étale at every
`w ∈ V` specializing `y`.

Proof. Put `I = 𝔭R'`.

- Every `𝔭^{n+1}` is nonzero, otherwise `𝔭` would be nil. So
  `nonempty_level_quotient` gives levels for `R' → R'/I^{n+1}`, using
  `(𝔭^{n+1})R' = I^{n+1}`.
- Artin–Rees in `R'` (`Ideal.exists_pow_inf_eq_pow_smul`) gives `c` with
  `𝔍 ∩ I^m ⊆ I𝔍` for `m ≥ c + 1`.
- If `I ⊆ P_w` and `VanN c w`, then `VanN n w` for all `n ≥ c` (`van_succ`).
  So `ξ` is infinitesimally étale at `w`, by `killAt_of_van` and
  `killAt_of_quotient`.
- `VanN c y` holds by `van_of_killAt`, since `ξ` is étale at `y`. Take the
  open set `V` of `exists_open_van`. It contains `y`.
- A point `w ∈ V` specializing `y` has `I ⊆ P_y ⊆ P_w`, so `VanN c w` holds.

This replaces Murre's formal scheme `Ŷ → F̂`. Murre uses the thickenings of
the closure of the image of `y` in `S`. Here the levels are the thickenings
`Spec (R/𝔭^{n+1})` of `V(𝔭)`, and the étale locus is controlled by the
single level `c`.
