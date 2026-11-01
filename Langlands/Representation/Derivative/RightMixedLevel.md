# Levels of subrepresentations of right mixed products

Module `Langlands.Representation.Derivative.RightMixedLevel`, namespace
`Langlands.Derivative.RightMixedLevel`.

Let `B` be a smooth representation of a mirabolic group all of whose nonzero
derivatives have order `s + 1`, and let `A` be a smooth representation of
`GL_(k+1)`. Suppose the left mixed product `Y = B^(s+1) × A|P` is homogeneous.
The main theorem, `level_of_injective_rightMixed`, says that every nonzero
subrepresentation of the right mixed product `B × A` then has level
`λ(Y) + s + 1`. This is Case 1 of the proof of Zelevinsky's Theorem 6.2
(`zelevinsky-1980-induced-ii`, Theorem 6.2 on printed p.188; proof in §6.3,
printed pp.188–189), in the form needed for the induction.

All the representation-theoretic inputs are **explicit hypotheses**: published
Library propositions with no published proof. Nothing here proves or assumes
their proofs.

| Hypothesis | Published proposition | Content |
| --- | --- | --- |
| `hE` | `Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T` | exactness of `Ψ⁻`, `Φ⁻` |
| `hD` | `RightMixedProductPhiMinusDetection.{uF, uV} F T` | BZ77 4.13(d) |
| `hS` | `MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T` | BZ77 4.13(c), the short exact sequence |
| `hB` | `MirabolicProductMinus.RightPhiBoundary.{uF, uV} F T` | BZ77 4.13(c), the `P_1` boundary case |

`hS` and `hB` are two components of the published
`MirabolicProductMinusCompatibilityStatement` (BZ77 Proposition 4.13(b,c)).
`hD` is a component of the published `MixedProductDerivativeStatement` module
(BZ77 4.13(d)). Exactness is used at carrier universe `max uF uV`, because the
mixed products have carriers in that universe.

## Provenance

This is internal derived material. It formalizes the Case 1 argument in
Zelevinsky's proof of Theorem 6.2 (§6.3 (2), printed pp.188–189, PDF
pp.25–26 of `zelevinsky-1980-induced-ii`). That proof refers to
Bernstein–Zelevinsky §4.15, Case 1 (`bernstein-zelevinsky-1977-induced-i`),
which applies Proposition 4.13(c,d) repeatedly; here it is applied `s + 1`
times. The induction on `s` and the explicit form of the
level are internal Lean packaging.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`, `T : F.TopologicalData` and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology` are fixed, with
`T.topology` installed. Factor carriers are in `Type uV`; products have
carriers in `Type (max uF uV)`. `mirabolic r F.Carrier` is `P_(r+1)`.
`T.rightMixedProductFunctor (k+1) r` sends `(B, A)` with `B` on `P_(r+1)` and
`A` on `GL_(k+1)` to `B × A` on `P_(k+1+r+1)`.
`T.leftMixedProductFunctor n k` sends a `GL_n` representation and a `P_(k+1)`
representation to their left mixed product on `P_(n+k+1)`. `Φ⁻`, `Ψ⁻` are the
published normalized `Mirabolic.phiMinus`, `Mirabolic.psiMinus`.

## Declarations

### Short exact sequences with a zero end (section `Maps`)

- `injective_of_range_eq_ker i q h`: if `range i = ker q` and the source of
  `i` is a subsingleton, then `q` is injective.
- `surjective_of_range_eq_ker i q h`: if `range i = ker q` and the target of
  `q` is a subsingleton, then `i` is surjective.

### Rank transports and one `Φ⁻` step (section `Cast`)

- `isHomogeneous_mirabolicRankCast`: rank transport preserves homogeneity.
- `mirabolicDerivative_zero_cast_obj`: the order-one derivative
  `mirabolicDerivative T ψ r 0` of the transport of `B` along `r = r + 0` is
  `Ψ⁻ B` (definitionally).
- `level_eq_succ_of_phiMinus h W hW`: for `h : a = M + 1`, if `Φ⁻` of the
  transported `W` is nontrivial then `λ(W) = λ(Φ⁻ W) + 1`
  (`LevelCalculus.level_eq_level_phiMinus_succ` and detection).
- `phiMinus_cast_map_injective hE h f hf`: `Φ⁻` after rank transport maps an
  injective intertwiner to an injective intertwiner (exactness).
- `nontrivial_phiMinus_of_injective hD B A f hf hW`: if `f : W ⟶ B × A` is
  injective and `W` is nontrivial, then `Φ⁻` of `W` (transported along
  `k + 1 + r = k + r + 1`) is nontrivial. This is `hD` (BZ77 4.13(d)), applied
  to the invariant subspace `range f` and transported through `W ≅ range f`.

### The level formula (section `Level`)

- `level_eq_of_phiMinus_injective h W X hX g hg hW`: if `Φ⁻ W` (after
  transport along `h : a = M + 1`) is nontrivial and injects by `g` into a
  homogeneous `X`, then `λ(W) = λ(X) + 1`.

The remaining two theorems take `hE hD hS hB`.

- `level_of_injective_rightMixed_zero k n A B hBj hY W f hf hW` (the case
  `s = 0`): let `A` be on `GL_(k+1)` and `B` on `P_(n+1)`. Suppose every
  nonzero derivative order of `B` is `1` (`hBj`), and suppose
  `Y = Ψ⁻B × Res A` is homogeneous (`hY`), where `Res A` is the restriction of
  `A` to `P_(k+1)`. Then every nontrivial `W` with an injection
  `f : W ⟶ B × A` has `λ(W) = λ(Y) + 1`. Proof:
  - `Φ⁻ W ≠ 0` by `hD`, and `Φ⁻ f` is injective by `hE`.
  - If `n = 0`, `hB` identifies `Φ⁻(B × A)` with `Ψ⁻B × Res A`
    (after transport).
  - If `n = R + 1`, `hS` gives the exact sequence
    `0 → Φ⁻B × A → Φ⁻(B × A) → Ψ⁻B × Res A → 0`.
    Here `Φ⁻B = 0`, because `B` has no nonzero derivative of order `≥ 2`
    (`LevelCalculus.nontrivial_phiMinus_iff`). So the first term vanishes
    (`ProductVanishing.subsingleton_rightMixed`), and the second map is
    injective.
  - In both cases `Φ⁻ W` injects into a transport of the homogeneous `Y`, and
    `level_eq_of_phiMinus_injective` concludes.
- `level_of_injective_rightMixed k n s r hr A B hBj hY L hL W f hf hW` (main
  theorem): let `r = n + s` (`hr`), `A` on `GL_(k+1)` and `B` on `P_(r+1)`.
  Suppose every nonzero derivative order of `B` is `s + 1` (`hBj`). Suppose
  the left mixed product
  `Y = B^(s+1) × Res A = (T.leftMixedProductFunctor n k).obj
  ((mirabolicDerivative T ψ n s).obj (cast B), Res A)` is homogeneous (`hY`).
  Then for every rank `L` with `hL : k + 1 + r = L`, every nontrivial
  `W` on `P_(L+1)` with an injection `f` into the transport of `B × A` along
  `hL` satisfies `λ(W) = λ(Y) + (s + 1)`.

  Proof, by induction on `s`. The case `s = 0` is the previous theorem. For
  `s + 1`, write `r = r' + 1`.
  - `Ψ⁻B = 0`, because order 1 is not `s + 2`. So in the exact sequence of
    `hS`, `0 → Φ⁻B × A → Φ⁻(B × A) → Ψ⁻B × Res A → 0`, the last term vanishes
    (`ProductVanishing.subsingleton_leftMixed`), and the first map is an
    isomorphism (`LevelCalculus.isIso_of_bijective`).
  - `Φ⁻B` has only the derivative order `s + 1`
    (`LevelCalculus.hasNonzeroDerivative_succ_iff`).
  - Its order-`(s+1)` derivative is, as an object, the order-`(s+2)`
    derivative of `B` (`LevelCalculus.mirabolicDerivative_succ_cast_obj`), so
    `Y` is unchanged.
  - `Φ⁻ W` is nontrivial (`hD`) and injects into `Φ⁻B × A` (by `hE` and the
    isomorphism). The induction hypothesis gives
    `λ(Φ⁻ W) = λ(Y) + s + 1`, and `λ(W) = λ(Φ⁻ W) + 1`.

The flexible rank parameters (`r` with `hr : r = n + s`, `L` with `hL`)
avoid definitional unfolding of rank arithmetic. Mathematically `L` is always
`k + 1 + r`.
