# Unitarizability of the shifted highest derivative

Authors: Worker 4876 (proof) and Worker 89 (verification and submission).
This module proves the published proposition
`Langlands.Classification.BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T`
(module `BernsteinShiftedHighestDerivativeUnitarizabilityStatement`). For every
`N > 0`, every unitary additive character `ψ`, every irreducible unitarizable
actual smooth representation `π` of `GL_N` with carrier in `Type (max uF uV)`
and every highest-derivative order datum `hd` of `π`, the shifted highest
derivative `ν^(1/2) π^(h)` (`shiftedHighestDerivative F T ψ hd`) is
unitarizable.

The final theorem is

```lean
theorem Langlands.Classification.bernsteinShiftedHighestDerivativeUnitarizability
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T
```

It has no hypotheses beyond the statement's own. There are no axioms beyond the
standard ones, no proof holes and no heartbeat changes. It is the conditional
theorem `bernsteinShiftedHighestDerivativeUnitarizability_of_phiMinusUnitarity`
below, applied to the published proof
`Langlands.Derivative.Mirabolic.mirabolicPhiMinusUnitarity` of
`Derivative.MirabolicPhiMinusUnitarity` (normalized `Φ⁻` preserves
unitarizability, Bernstein 1984 §9.3(ii); module
`Derivative.MirabolicPhiMinusUnitarityProof`). The irreducibility of `π` is
not used.

The route is Bernstein 1984, §7.2–§7.4, made concrete for the unitarizability
half. Restrict `π` to the mirabolic `P_N`, which keeps unitarizability. Apply
`Φ⁻` `h - 1` times, which keeps unitarizability by `hΦ`. Every derivative of
order above `h` vanishes, so the radical acts trivially on the result `τ`.
Then `Ψ⁻ τ` is the Levi restriction of `τ` twisted by `|det|^(-1/2)`. The
shift `ν^(1/2)` cancels that twist, so `ν^(1/2) Ψ⁻ τ` embeds in the Levi
restriction of `τ`, which is unitarizable.

## Helper lemmas (namespace `Langlands.Classification.ShiftedHighestDerivative`)

- `isUnitarizable_twist_of_iso`: if `A ≅ B` are smooth representations and the
  twist of `B` by a character `χ` with open kernel is unitarizable, so is the
  twist of `A`. The twisted isomorphism (`twistIntertwining`) is an injective
  intertwining map into a unitarizable representation, so
  `IsUnitarizable.of_injective` applies.

- `isUnitarizable_segmentFactor_psiMinus T n X hrad hX`. Here `X` is a
  smooth representation of `P_(n+1)` = `mirabolic n F.Carrier`, the radical
  acts trivially on `X` (`hrad`), and `X` is unitarizable (`hX`). The
  conclusion is that `T.segmentFactor (Ψ⁻ X) (1/2)` is unitarizable. The
  identity of `X` descends to a linear map `f` from the radical coinvariants
  to `X` (`Jacquet.Localization.lift`), because the radical acts trivially.
  `f` sends the class of `v` to `v`, so it is injective, since `mk` is
  surjective. In `T.segmentFactor (Ψ⁻ X) (1/2)`, the element `g` of `GL_n`
  acts on a class by `|det g|^(1/2) · |det g|^(-1/2) · [levi g · v]`. The two
  scalars multiply to `1` (`realPowerCharacter_add`,
  `realPowerCharacter_zero`). So `f` intertwines this action with
  `X ∘ levi`. That composite is unitarizable by `IsUnitarizable.comp`, and
  `of_injective` concludes.

- `subsingleton_rankCast_phiMinus`. Let `h : a = n' + i` and
  `h' : a + 1 = n' + (i + 1)`. If the derivative with `i + 1` `Φ⁻` steps
  of `X` on `P_(a+2)`, after the rank transport along `h'`, is zero, then the
  derivative with `i` `Φ⁻` steps of `Φ⁻ X`, after the rank transport along `h`,
  is zero. After
  `subst h`, both sides are the same representation by definition:
  `mirabolicDerivative T ψ n' k` is `phiMinusIterate T ψ n' k ⋙ Ψ⁻`, and
  `phiMinusIterate` with `i + 1` steps unfolds to `Φ⁻` followed by `i` steps.

- `shiftedDerivativeUnitarity_core T ψ hΦ j`, by induction on `j`. Let `A` be a
  unitarizable representation of `P_(n+j+1)`. Suppose every derivative of `A`
  with `i` `Φ⁻` steps, where `n + j = n' + i` and `n' < n`, is zero after
  rank transport.
  Here `j` counts `Φ⁻` steps, so these are the derivatives of order above
  `j + 1`. Then
  `T.segmentFactor (mirabolicDerivative T ψ n j A) (1/2)` is unitarizable.
  - `j = 0`. The derivative is `Ψ⁻ A`. For `n = 0`, the radical is trivial
    (`radical_acts_trivially_zero`). For `n = m + 1`, the vanishing hypothesis
    gives that every derivative of `Φ⁻ A` is zero
    (`subsingleton_of_forall_mirabolicDerivative`). Then
    `radical_acts_trivially_of_phiMinus` (from `MirabolicHighestDerivativeDescent`)
    shows that the radical acts trivially on `A`.
    `isUnitarizable_segmentFactor_psiMinus` concludes.
  - `j + 1`. The derivative with `j + 1` `Φ⁻` steps of `A` is by definition
    the derivative with `j` `Φ⁻` steps of `Φ⁻ A`. The induction hypothesis applies to
    `Φ⁻ A`. It is unitarizable by `hΦ`, and its higher derivatives vanish by
    `subsingleton_rankCast_phiMinus`.

- `shiftedDerivativeUnitarity_cast`: the same after an arbitrary rank
  transport `N = n + j` (`subst`, then the core lemma).

- `isUnitarizable_shiftedHighestDerivative T ψ hΦ π hπ hd`, for unitarizable
  `π` on `GL_(n+1)` and highest-order data `hd`. Its conclusion is
  `T.segmentFactor (generalLinearDerivative T ψ (n+1) hd.order _ π) (1/2)`
  unitarizable. The Library isomorphism `generalLinearRestrictionDerivativeIso`
  (`Derivative.RankCastCompat`) identifies the `GL` derivative with the
  rank-transported mirabolic derivative of the restriction of `π` to
  `P_(n+1)`. `isUnitarizable_twist_of_iso` transfers along it. The
  restriction is unitarizable by `IsUnitarizable.comp` along the subgroup
  inclusion. Its higher derivatives vanish: `hd.higher_vanish` gives the
  vanishing of the `GL` derivatives of higher order. The same isomorphism
  transports this to the mirabolic side.
  `subsingleton_rankCast_mirabolicDerivative_congr` changes the rank transport
  equation. Then `shiftedDerivativeUnitarity_cast` applies with
  `j = hd.order - 1`.

## Final theorems

`bernsteinShiftedHighestDerivativeUnitarizability_of_phiMinusUnitarity F T hΦ`
takes `hΦ : Derivative.MirabolicPhiMinusUnitarity.{uF, uV} F T`. It introduces
`N`, `0 < N`, `ψ`, `π`, irreducibility (unused), unitarizability and `hd`. It
writes `N = n + 1` and applies `isUnitarizable_shiftedHighestDerivative` with
`hΦ ψ`. `shiftedHighestDerivative F T ψ hd` unfolds to exactly that
representation.

`bernsteinShiftedHighestDerivativeUnitarizability F T` applies the conditional
theorem to `Derivative.Mirabolic.mirabolicPhiMinusUnitarity.{uF, uV} F T`.

## Sources

J. N. Bernstein, *P-invariant distributions on GL(N) and the classification of
unitary representations of GL(N) (non-archimedean case)*, LNM 1041 (1984):
§7.2 (derivatives and depth, p.82), §7.4 (p.83) and §9.3(ii) (p.97). The
Lean proof does not follow Bernstein's argument through the P-module criterion
of §7.3. It uses only the forward unitarity of `Φ⁻` and the vanishing of the
higher derivatives.
