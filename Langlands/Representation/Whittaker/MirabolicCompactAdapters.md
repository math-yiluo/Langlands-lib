# Character-change and determinant-twist adapters for compact induction

Author: Worker 805.

This module supplies two actual equivariant maps on compactly induced
representations, first for a general inducing subgroup and then for the
actual compact mirabolic model `Whittaker.mirabolicCompactInduced ψ n`
(BZ76's `τ_P⁰`, JPSS's `τ_r`). They are the two compact-model adapters
needed by the compact twisted-pairing target
`Langlands.Whittaker.MirabolicCompactTwistedPairingStatement`: the
opposite-character model of JPSS (1983), §1.5, p.384, is connected to the
same-character model, and the determinant twist `α^s` of JPSS
pp.380–384 is moved between the representation and the covariance of a
bilinear form. The module proves no pairing statement itself.

Everything here is derived from the published definitions in
`Langlands.Representation.Induction.Definitions`,
`Langlands.Representation.Whittaker.MirabolicModels`,
`Langlands.Representation.Whittaker.CharacterChange` and
`Langlands.Representation.Filtration.InvariantBilinear`. No hypothesis is a
character-change or twist equivalence; each map is constructed and its
covariance, local constancy (fixed open subgroup) and compact projected
support are proved.

## General compact induction (`Langlands.Induction`)

Let `G` be a topological group, `P` a subgroup and `σ` a representation of
`P` over a commutative ring `R`. The carrier `CompactFunctions P σ` consists of
functions `f : G → V` with `f (p * g) = σ p (f g)`, fixed by some open
subgroup under right translation, with compact image of their support in
`P \ G` (`quotientSupport`). The action is right translation.

**Left translation by a normalizing element.** For `d` with `d` and `d⁻¹` in
the normalizer of `P`:

- `quotientLeft P d hd : P \ G → P \ G`, `[x] ↦ [d * x]`, is well defined and
  continuous (`continuous_quotientLeft`, `quotientLeft_mk`).
- `normalizerConj P d hd p = d * p * d⁻¹ ∈ P`.
- If `σ' p = σ (d * p * d⁻¹)` for all `p : P`, then
  `compactLeftTranslate P σ σ' d hd hd' hσ` sends `f` to `g ↦ f (d * g)`.
  Covariance follows from `f (d * p * g) = f ((d p d⁻¹) * (d * g))`; the same open
  subgroup fixes the translate; the projected support of the translate is the
  image of that of `f` under the continuous map `quotientLeft P d⁻¹`, hence
  compact (private lemma `leftTranslate_support`). Left and right
  translations commute, so the map intertwines.
- `compactLeftTranslateEquiv` is the resulting equivalence
  `(compactInduced P σ).Equiv (compactInduced P σ')`, with inverse left
  translation by `d⁻¹`.

**Multiplication by a character trivial on `P`.** Let `χ : G →* Rˣ` have open
kernel and satisfy `χ p = 1` on `P`.

- `kernelOpenSubgroup χ hχ` is `ker χ` as an open subgroup.
- `compactCharacterMultiply P σ χ hP hχ` sends `f` to `g ↦ χ g • f g`.
  Covariance uses `χ (p * g) = χ g`; if `K` fixes `f` then `K ⊓ ker χ` fixes
  the product; the support is unchanged because `χ g` is a unit
  (private lemma `characterMultiply_support`).
- `compactCharacterMultiplyEquiv P σ χ hP hχ` is an equivalence
  `(twist χ (compactInduced P σ)).Equiv (compactInduced P σ)`, where
  `Langlands.twist χ ρ g = χ g • ρ g`; its inverse multiplies by `χ⁻¹`
  (`χ⁻¹` is again trivial on `P` with open kernel). The intertwining identity is
  `χ x • χ h • f (x * h) = χ (x * h) • f (x * h)`.

## Bilinear forms (`Langlands.InvariantBilinear`)

For a field `k`, `forms ρ σ κ` is the published submodule of bilinear maps `B`
with `B (ρ g v) (σ g w) = κ g * B v w`.

- `twistLeftEquiv χ ρ σ κ κ' h`: if `κ g = χ g * κ' g` for all `g`, then
  `forms (twist χ ρ) σ κ ≃ₗ[k] forms ρ σ κ'`, with the same underlying bilinear
  map; the unit `χ g` cancels.
- `equivRight ρ χ e`: an equivalence `e : σ.Equiv τ` in the second argument
  transports `forms ρ σ χ ≃ₗ[k] forms ρ τ χ`, by `flipEquiv`, the published
  `equivLeft`, and `flipEquiv` again.

`Langlands.Induction.formsCharacterShift P σ σ' χ hP hχ κ κ' h` combines these:
for compact induction on the left and `κ = χ κ'`,
`forms (compactInduced P σ) σ' κ ≃ₗ[k] forms (compactInduced P σ) σ' κ'`.

## The actual compact mirabolic model (`Langlands.Whittaker`)

Here `P = mirabolic n F ⊂ GL_{n+1}(F)`, `N = Mirabolic.upperUnipotent n F`,
`θ = mirabolicCharacter ψ n`.

**Character change (BZ76 §5.6, p.45).** BZ76 observe that every nondegenerate
character of `U` is conjugate to the standard one by a diagonal matrix in `P`.
The published `characterChangeElement a n = diag(a^n, …, a, 1)` lies in `P`
(`mirabolicCharacterChangeElement a n`), with inverse
`mirabolicCharacterChangeElement a⁻¹ n`, and normalizes `N`
(`mirabolicCharacterChangeElement_mem_normalizer`).
By the published `standardCharacter_characterChangeConj`, conjugation by it
turns `θ_ψ` into `θ_{ψ.scale a}`, where `ψ.scale a x = ψ (a * x)`
(`mirabolicCharacter_characterChange`). Hence

```text
mirabolicCharacterChangeEquiv ψ a n :
  (mirabolicCompactInduced ψ n).Equiv (mirabolicCompactInduced (ψ.scale a) n),
  f ↦ (g ↦ f (d_a * g)).
```

For `a = -1`, `d_{-1}` has alternating entries `±1` and last entry `1`, and
`ψ.scale (-1)` is the opposite character `x ↦ ψ(-x)`; this is the map that
identifies JPSS's opposite-character compact induction (§1.5, p.384) with the
same-character model.

**Determinant twist (JPSS §1.5, pp.380–384, `α^s` twists).** For an absolute
value `abv` on `F` and `c : ℂ`, `mirabolicDeterminantCharacter abv n c` is
`g ↦ (abv (det g) : ℂ)^c` on `P` (the published `Shahidi.determinantPower`
restricted to `P`; its value is `determinantWeight abv g.val c`). It is trivial
on `N` because unipotent matrices have determinant `1`
(`mirabolicDeterminantCharacter_unipotent`), and its kernel is open whenever
`Shahidi.IsOpenNormOne abv` holds (`isOpen_ker_mirabolicDeterminantCharacter`).
Then

```text
mirabolicDeterminantTwistEquiv hopen ψ n c :
  (twist |det|^c (mirabolicCompactInduced ψ n)).Equiv (mirabolicCompactInduced ψ n),
  f ↦ (g ↦ |det g|^c * f g),
mirabolicFormsDeterminantShift hopen ψ n σ' c κ κ' h :
  forms (mirabolicCompactInduced ψ n) σ' κ ≃ₗ[ℂ]
    forms (mirabolicCompactInduced ψ n) σ' κ'
```

whenever `κ g = |det g|^c * κ' g`. With `κ g = |det g|^(-s)`, `κ' = 1` and
`c = -s`, this removes the covariance `|det|^(-s)` of the target statement,
i.e. JPSS's `Bil_P(τ_r ⊗ α^s, τ_r) ≅ Bil_P(τ_r, τ_r)`.
