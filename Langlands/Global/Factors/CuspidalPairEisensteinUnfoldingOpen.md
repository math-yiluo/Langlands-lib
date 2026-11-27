# Integration over the open cell

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingOpen` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) rewrites an integral over a fundamental domain
of the open-cell stabilizer `Λ_(J₀)(F)` in `N₀(𝔸)` as an iterated integral. The outer integral runs
over the radical `U'(𝔸)`. The inner one runs over a fundamental domain of the rational block
diagonal group `N_(t+1)(F) × N_(r+1)(F)`. This is the two-block `GL_N` analogue of the open-cell
step of Shahidi, *Functional equation satisfied by certain L-functions*, Compositio Math. 37 (1978),
proof of Lemma 2.1, paragraph after (2.10.3), p. 182: the integral over `N_(M')(F) \ N₀(𝔸)` is split
as an integral over `U'(𝔸)` and over `N_(M')(F) \ N_(M')(𝔸)`. These correspond to the source's
`N^V_𝔸` and `V_𝔸 / V_F` for the open class.

## Measures

- Borel instances on the products, s-finiteness of `haarN`, `haarM`, `haarH`
  (`haarN_sFinite`, `haarM_sFinite`, `haarH_sFinite`), and their left invariance
  (`haarN_isMulLeftInvariant`, `haarM_isMulLeftInvariant`, `haarH_isMulLeftInvariant`).
- `radicalConj m`: conjugation `Y ↦ m Y m⁻¹` of the radical by the block diagonal group, the
  Library's `LeftCosetSpace.Semidirect.conj` (`radicalHom_radicalConj`,
  `continuous_radicalConj_uncurry`).
- `map_radicalConj_haarN`: conjugation preserves `haarN`. Its modulus is one by the Library's
  `LeftCosetSpace.Semidirect.mulEquivHaarChar_conj_eq_one_of_finiteCovolume`, since both
  lattices have finite covolume.
- `skewHomeomorph`: the change of variables `(Y, m) ↦ (m⁻¹ Y m, m)`. `openProd_eq_skew`:
  `u'(Y) diag(m) = diag(m) u'(m⁻¹ Y m)`. `measurePreserving_skewHomeomorph`: it preserves
  `haarN × haarM`, by Mathlib's `MeasurePreserving.skew_product` and `map_radicalConj_haarN`.

## Fundamental domains

- `fundamentalDomain_eq_univ`: the Library's fundamental domain of the trivial subgroup is
  everything.
- `fdM`: the Library's fundamental domain of `N_(t+1)(F) × N_(r+1)(F)` in the block diagonal
  group.
- `openDomain = openProd '' (univ ×ˢ fdM)`, the set `{u'(Y) diag(m) : m ∈ fdM}`. It is a
  measurable strict fundamental domain of `Λ_(J₀)(F)` (`existsUnique_mem_openDomain`,
  `measurableSet_openDomain`). This is the Library's
  `LeftCosetSpace.Semidirect.productFundamentalDomain_unique`, using
  `comap_radicalHom_openLattice` (the radical meets `Λ_(J₀)(F)` trivially).

## Result

`setIntegral_eq_iterated_open`: let `f₀ : N₀(𝔸) → ℂ` be left `Λ_(J₀)(F)`-invariant and
integrable for `haarH` on a measurable strict fundamental domain `D` of `Λ_(J₀)(F)`. Then
`(Y, m) ↦ f₀(diag(m) u'(Y))` is integrable for `haarN × haarM|_fdM`, and

```text
∫_D f₀ dhaarH = ∫_Y ∫_{m ∈ fdM} f₀(diag(m) u'(Y)) dhaarM dhaarN.
```

The steps are as follows. The integral over `D` equals the integral over `openDomain`
(Mathlib's `IsFundamentalDomain.setIntegral_eq`). That integral transports along `openProd`
by `haarH_eq_map_prod`. The change of variables `skewHomeomorph` then gives the integrand
`f₀(diag(m) u'(Y))`, and Fubini gives the iterated integral.
