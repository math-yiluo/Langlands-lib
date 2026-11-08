# Delta functions in compact induction from a character

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`. It belongs to the proof of
the pairing input `DeltaPairingStatement` (see `DeltaPairing` and `DeltaPairingGL`).

Throughout, `N` is a subgroup of a group `G`, `θ : N →* ℂˣ` is a character, and `K` is a
subgroup of `G`.

## Delta functions

- `IsGood N θ K g` means that `θ n = 1` for every `n ∈ N` with `g⁻¹ n g ∈ K`, so `θ` is trivial
  on `N ∩ g K g⁻¹`.
- `deltaFun N θ K g` is the function with value `θ(n)` at `n g k` (`n ∈ N`, `k ∈ K`) and `0` off
  `N g K`. The definition uses a chosen decomposition. When `g` is good the value does not
  depend on the decomposition (`deltaFun_apply`).
- `deltaFun_eq_zero`: the function vanishes off `N g K`.
- For good `g`:
  - `deltaFun_left`: `δ(m x) = θ(m) δ(x)` for `m ∈ N`.
  - `deltaFun_right`: `δ(x k) = δ(x)` for `k ∈ K`.
- Goodness is unchanged by moving `g` within `N g K` (`isGood_mul_left`, `isGood_mul_right`) and
  passes to smaller subgroups (`IsGood.mono`).
- Changing the base point changes the delta function by a scalar:
  - `deltaFun_mul_left`: the delta function at `m g` is `θ(m)⁻¹` times the one at `g`;
  - `deltaFun_mul_right`: the delta function at `g k` equals the one at `g`.

## Delta vectors

Let `G` be a topological group. If `K` is a compact open subgroup and `g` is good, then
`deltaVector K hK g hg` is the delta function as a vector of `c-Ind_N^G θ`
(`Induction.CompactFunctions N (characterRepresentation θ)`), and `eval_deltaVector` evaluates
it. Its covariance and smoothness are `deltaFun_left` and `deltaFun_right`. Its support modulo
`N` lies in the image of the compact set `g K`, and the projected support is closed
(`isClosed_quotientSupport`), so it is compact.

## Integration against delta functions

- `IsInverseEquivariant θ f` means `f(n x) = θ(n)⁻¹ f(x)` for `n ∈ N`.
- For such `f`, the product `δ · f` is left `N`-invariant (`deltaFun_mul_invariant`), so it
  descends to `N \ G`.
- If `f` is also right `K`-invariant, the descended product is the indicator function of the
  coset image `orbit N K g` (the image of `g K` in `N \ G`) with constant value `f(g)`
  (`descend_deltaFun_mul_eq_indicator`).
- `integral_deltaFun_mul`: for any measure `ν` on `N \ G` with open sets measurable and `K`
  open, `∫ δ · f dν = ν(orbit N K g) · f(g)`.
