# The relative effective Cartier locus of a flat closed subscheme of a proper flat family

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705).
This is a prerequisite statement under Task 5705, as permitted by the operator's
answer to request `98389b48910e54088e0e2b2ba6aaad9c`. Together with
`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement`, it is one of
the two hypotheses of a planned reduction of the published
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`
(Task 6002).

## Statement

`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement.{u}`
is a proposition with no proof asserted here.

**Data and hypotheses.** It quantifies over schemes `B` and `Y` in universe `u`,
a morphism `q : Y ⟶ B` and an ideal sheaf `Z : Y.IdealSheafData`. It assumes

- `IsLocallyNoetherian B`;
- `IsProper q` and `Flat q`;
- `Flat (Z.subschemeι ≫ q)`: the closed subscheme of `Z` is flat over `B`.

**Conclusion.** There is an open subscheme `U : B.Opens` with the following
property. Let `T`, `YT` be schemes, and let `g : T ⟶ B`, `qT : YT ⟶ T` and
`gY : YT ⟶ Y` form a pullback square, `IsPullback gY qT q g`:
```
YT --gY--> Y
|qT        |q
v          v
T  --g---> B
```
Then the pulled-back ideal `Z.comap gY` on `YT` is a relative effective Cartier
ideal for `qT` (`IsRelativeEffectiveCartierIdeal qT (Z.comap gY)`) if and only
if `g` lands in `U` (`Set.range g.base ⊆ U`).

Here `IsRelativeEffectiveCartierIdeal qT I` is the Library predicate from
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor`. It says that the
kernel module of `I.subschemeι` is locally free of rank one, so `I` is an
invertible ideal, and that `I.subschemeι ≫ qT` is flat. `Z.comap gY` is
Mathlib's pullback of ideal sheaves; its closed subscheme is the base change of
the closed subscheme of `Z` along `gY`.

The test scheme `T` is arbitrary: it need not be locally noetherian. Three
special squares illustrate the statement.

- The identity square `g = 𝟙 B`, `qT = q`, `gY = 𝟙 Y`. Since
  `Z.comap (𝟙 Y) = Z`, it shows: `Z` is a relative effective Cartier ideal for
  `q` if and only if `U = ⊤`.
- The square of the inclusion `g = U.ι : U ⟶ B`, with `YT = Y ×_B U` (for
  example `pullback q U.ι`) and its two projections. Since
  `Set.range U.ι.base = U`, it shows that the restriction of `Z` to
  `q⁻¹ U ≅ Y ×_B U` is a relative effective Cartier ideal over `U`.
- More generally, the square of the inclusion `V.ι` of any open subscheme
  `V ⊆ B` shows that the restriction of `Z` over `V` is a relative effective
  Cartier ideal if and only if `V ≤ U`. So `U` is the largest open subscheme
  over which `Z` is a relative effective divisor.

## Sources

S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`):

- Conventions, p.15: all schemes are locally noetherian.
- 3.1 (p.22): a closed subscheme is an effective (Cartier) divisor if its ideal
  is invertible. Definition 3.3 (p.22): a relative effective divisor on `X/S`
  is an effective divisor that is `S`-flat.
- Lemma 3.4 (p.22, proof pp.22–23): for a closed subscheme `D ⊂ X`, a point
  `x ∈ D` over `s ∈ S`, the following are equivalent. (i) `D` is a relative
  effective divisor near `x`. (ii) `X` and `D` are `S`-flat at `x`, and the
  fibre `D_s` is an effective divisor on `X_s` at `x`. (iii) `X` is `S`-flat at
  `x`, and `D` is cut out at `x` by one element that is regular on the fibre
  `X_s`.
- The paragraph after Definition 3.6 (p.23): if `D` is a relative effective
  divisor on `X_T/T` and `T' ⟶ T` is any map, then `D_{T'}` is a relative
  effective divisor on `X_{T'}/T'`. The argument uses only the `T`-flatness of
  `D` and the invertibility of its ideal.
- Theorem 3.7 (p.23) and its proof (p.24). Let `W ⊂ X × H` be the universal
  subscheme of the Hilbert scheme and `q : W ⟶ H` the projection. Let `V` be
  the open set of points of `W` at which `W` is an effective divisor, put
  `Z := q(W − V)`, closed because `q` is proper, and `U := H − Z`. Then
  `q⁻¹ U` is a relative effective divisor over `U`. Conversely, if
  `g : T ⟶ H` pulls `W` back to a relative effective divisor `D`, then for
  each `t ∈ T` the fibre `D_t = W_{g(t)} ⊗ k_t` is an effective divisor.
  Since a field extension is faithfully flat, so is `W_{g(t)}`. Lemma 3.4 then
  shows that `W` is a relative effective divisor along the fibre over `g(t)`,
  so `g(t) ∈ U`.

The statement has provenance *derived*. Kleiman's proof of Theorem 3.7 uses
only these properties of the pair `(Hilb, W)`: `X × H ⟶ H` is proper and flat,
`W` is flat over `H`, and `H` is locally noetherian. It never uses the universal
property of `Hilb` in the openness argument. The statement isolates this
argument for an arbitrary proper flat `q : Y ⟶ B` over a locally noetherian
`B` and a `B`-flat closed subscheme `Z ⊆ Y`. Here `Y` plays the role of `X × H`;
the projection `W ⟶ H` of Kleiman is `Z.subschemeι ≫ q`, which is proper because
`q` is proper and `Z.subschemeι` is a closed immersion.

## Derivation

These steps outline a proof. They are not Lean proofs.

1. **The locus.** Let `V ⊆ Y` be the set of points `y` with an open
   neighbourhood on which `Z` is an effective Cartier ideal; it is open. Points
   outside the closed subscheme of `Z` lie in `V`, since there the ideal is the
   unit ideal. So `Y − V` is a closed subset of the closed subscheme of `Z`.
   Put `U := B − q(Y − V)`. It is open because `q` is proper, hence closed.
2. **`g` lands in `U` ⇒ Cartier.** Over `q⁻¹ U ⊆ V` the ideal `Z` is invertible
   and its closed subscheme is flat over `U`. Factor `g` through `U`. The square
   for `g` is the composite of the square for `T ⟶ U` with the restriction of
   `q` to `q⁻¹ U`. By Kleiman's base-change paragraph after Definition 3.6,
   `Z.comap gY` is a relative effective Cartier ideal for `qT`. This direction
   needs no noetherian hypothesis on `T`.
3. **Cartier ⇒ `g` lands in `U`.** Let `t ∈ T` with residue field `k_t`, and
   `b = g(t)`. The fibre of `Z.comap gY` over `t` is an effective divisor in
   the fibre `YT_t`, by base change of the relative effective divisor along
   `Spec k_t ⟶ T`. This fibre is the base change of the fibre `Z_b ⊆ Y_b`
   along the field extension `k_b ⟶ k_t`, which is faithfully flat. So `Z_b`
   is an effective divisor on `Y_b`. Since `B` is locally noetherian and `q` is
   of finite type, `Y` is locally noetherian. At every point `y` of `Z` over
   `b`, condition (ii) of Lemma 3.4 holds: `Y` and the closed subscheme of `Z`
   are flat over `B`. So (i) holds, `y ∈ V`, and hence `b ∈ U`. Again `T` need
   not be noetherian.

## Relation between the Lean statement and the sources

- **Effective divisors as ideals.** Kleiman's "closed subscheme `D` whose ideal
  is invertible" is an ideal sheaf whose kernel module is locally free of rank
  one (`Picard.IsEffectiveCartierIdeal`). Relative effective divisors add flatness
  of the closed subscheme over the base (`Picard.IsRelativeEffectiveCartierIdeal`).
- **Base change as a pullback square.** Kleiman's `X_T` and `g_X⁻¹ W` are
  expressed by an arbitrary pullback square `IsPullback gY qT q g` and
  `Z.comap gY`. Any pullback square may be used, not only the chosen
  `pullback q g`, so the statement applies directly to squares such as
  `X ×_S T ⟶ X ×_S H` over `T ⟶ H`.
- **Test schemes.** Kleiman's tests are locally noetherian. The statement
  allows every `T : Scheme.{u}`. Steps 2 and 3 above use the noetherian
  hypothesis only on `B` and `Y`, where Lemma 3.4 is applied.
- **Generality.** Kleiman states the openness only for `Y = X × Hilb_{X/S}` and
  the universal subscheme. The statement replaces `Hilb_{X/S}` by an arbitrary
  locally noetherian `B` and asks only that `q` be proper and flat and that `Z`
  be flat over `B`. These are the properties the proof uses.

## Use

In the planned reduction of `Picard.RelativeEffectiveDivisorHilbertPiecesStatement`,
`B` is the Hilbert scheme `H` of `HilbertSchemeUniversalFamilyStatement`, `q` is
`pullback.snd f πH : X ×_S H ⟶ H` and `Z` is the universal ideal `W`. The open
`U` is Kleiman's `Div_{X/S}`.
