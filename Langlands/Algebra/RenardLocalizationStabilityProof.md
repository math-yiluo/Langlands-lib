# Proof of actual-localization stability and the canonical stable image

Author: Worker 977, for proof task `c9d7a084-4b9f-4094-a4d9-88126e384078`.
This module proves the published statement module
`Langlands.Algebra.RenardLocalizationStabilityStatements`, which it imports
by name and leaves unchanged. The exported theorem

`Langlands.Renard.EndomorphismLocalization.actualLocalizationStabilityStatements`

has the complete closed type
`Langlands.Renard.EndomorphismLocalization.ActualLocalizationStabilityStatements.{uR,uV}`,
with no section parameters and no extra premise. The coefficient universe
`uR` and the carrier universe `uV` are independent. All data are actual:
the public `Localized a`, `iota a`, `localizedEnd a`, `localizedEquiv a`
and `frac` from `Langlands.Algebra.RenardEndomorphismLocalization`, used
unchanged, over an arbitrary commutative ring `R` and an ordinary unital
`R`-module `V`. Zero rings, zero modules and modules of any size are
included. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

This is an internal derived result. David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, Appendix
C.II, final proposition and proof, printed page 279 / PDF page 285,
motivates it. The definition of stability is on printed page 276 / PDF
page 282, and the actual localization is A.III.1, example 5, with the
following lemma and corollary, printed pages 252–253 / PDF pages 258–259.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement Markdown records the provenance of the targets. The proof
below does not follow Renard's integrality argument in End_B(L_a). The
Noetherian part uses the published quotient-Hopfian Noetherian core. The
stable-image part is a direct Fitting argument without finiteness.

## Imports

- `Langlands.Algebra.RenardLocalizationStabilityStatements`: the target,
  and through it the actual localization construction.
- `Langlands.LinearAlgebra.NoetherianLocalizationCoreProof`: the published
  internal Noetherian core. The proof uses `localization_core` and
  `intertwines_pow` from namespace
  `Langlands.LinearAlgebra.NoetherianLocalizationCore`.

The module also imports
`Langlands.Algebra.RenardEndomorphismLocalizationKernelProof` and reuses
`Langlands.Renard.EndomorphismLocalization.iota_eq_zero_iff` for the
pointwise kernel criterion. The separate `power_exhaustion` helper below
retains its automorphism-power formulation and follows directly from the
public fraction lemmas.

## Implemented proof

The locally defined helper theorems are in namespace
`Langlands.Renard.EndomorphismLocalization.StabilityProof`. The four closed
theorems are in `Langlands.Renard.EndomorphismLocalization`.

### Kernel criterion and exhaustion

- The imported `EndomorphismLocalization.iota_eq_zero_iff` states
  `iota a z = 0 ↔ ∃ k, (a ^ k) z = 0`. Its proof uses
  `iota a z = frac a z 0` (`frac_zero`) and `0 = frac a 0 0`. The fraction
  equality criterion `frac_eq_frac_iff` with both denominators `X ^ 0`
  turns this into `∃ k, (a ^ k) z = (a ^ k) 0`.
- `localizedEquiv_pow_apply`: powers of the automorphism
  `localizedEquiv a` act as the same powers of `localizedEnd a`. Both are
  iterates of the same function.
- `iota_pow_apply`: `iota a ((a ^ m) x) = (localizedEnd a ^ m) (iota a x)`.
  It is `intertwines_pow` applied to `iota_intertwines`.
- `power_exhaustion`: each `y : Localized a` is some `frac a v m` by
  `frac_surjective`, and `localizedEnd_pow_frac` gives
  `(localizedEquiv a ^ m) y = iota a v`.

### Item 1: `noetherianActualLocalizationStatement`

`noetherian_actual` assumes `[IsNoetherian R V]` and
`[IsNoetherian R (Localized a)]`. It applies `localization_core` with
`M = V`, `N = Localized a`, `e = localizedEquiv a` and `f = iota a`. The
three hypotheses are `iota_intertwines`, `power_exhaustion` and the forward
direction of `iota_eq_zero_iff`. The conclusion is literally
`Function.Surjective (iota a)` together with one `n` such that `0 < n`,
`ker (iota a) = ker (a ^ n)`, `ker (a ^ n) = ker ((a ^ n) ^ 2)` and
`range (a ^ n) = range ((a ^ n) ^ 2)`. The closed theorem introduces
`R`, `V`, `a` and the two Noetherian hypotheses as instances and applies
`noetherian_actual`.

### Item 2: `stablePowerImageStatement`

Fix `n` with `0 < n`, `hk : ker (a ^ n) = ker ((a ^ n) ^ 2)` and
`hr : range (a ^ n) = range ((a ^ n) ^ 2)`. Write `S = range (a ^ n)`.

- `pow_apply_eq_zero_of_succ`: if `a ^ (n + 1)` kills `x`, then so does
  `(a ^ n) ^ 2 = a ^ ((n - 1) + (n + 1))`, using `0 < n`. By `hk`,
  `a ^ n` kills `x`.
- `pow_apply_eq_zero_of_pow`: by induction on `k`, `a ^ (n + k)` killing
  `y` implies `a ^ n` kills `y`. The step applies the induction hypothesis
  to `a y` and then the previous lemma. Hence `(a ^ m) x = 0` implies
  `(a ^ n) x = 0` for every `m`.
- `isCompl_ker_range`: the Fitting decomposition
  `IsCompl (ker (a ^ n)) S`. For disjointness, if `(a ^ n) y` lies in the
  kernel then `y ∈ ker ((a ^ n) ^ 2) = ker (a ^ n)`, so `(a ^ n) y = 0`.
  For codisjointness, `hr` writes `(a ^ n) v = ((a ^ n) ^ 2) w`, and then
  `v = (v - (a ^ n) w) + (a ^ n) w` with the first summand in the kernel.
  This lemma does not use `0 < n`.
- `apply_mem_range`: `S` is `a`-invariant, since `a ^ n * a = a * a ^ n`.
- `exists_apply_eq` and `exists_pow_apply_eq`: `a`, and hence every
  `a ^ m`, maps `S` onto `S`. By `hr` an element of `S` is
  `((a ^ n) ^ 2) w = a ((a ^ n) ((a ^ (n - 1)) w))`, using
  `2 n = 1 + (n + (n - 1))` for `0 < n`. The power version is by induction
  on `m`.
- `eq_zero_of_pow_apply_eq_zero`: if `s = (a ^ n) y ∈ S` and
  `(a ^ k) s = 0`, then `a ^ (k + n)` kills `y`. So `a ^ n` kills `y`, that
  is, `s = 0`.
- `iota_comp_subtype_injective`: the restriction
  `g = (iota a).comp S.subtype` has trivial kernel. If `iota a s = 0`, the
  kernel criterion gives a power of `a` killing `s`, so `s = 0`.
- `iota_comp_subtype_surjective`: write `y = frac a v m`. The decomposition
  gives `v = k₀ + s₀` with `k₀ ∈ ker (a ^ n)` and `s₀ ∈ S`, and
  `s₀ = (a ^ m) t` with `t ∈ S`. Then `iota a k₀ = 0`, and applying the
  injective map `localizedEquiv a ^ m` reduces `iota a t = frac a v m` to
  `localizedEnd_pow_frac` and `iota_pow_apply`.
- `stablePowerImageAt_of_stable`: `e` is the inverse of
  `LinearEquiv.ofBijective g`. Then `e.symm s = iota a s` holds by
  definition, which is the second equation
  `e.symm.toLinearMap = (iota a).comp S.subtype`. For the first equation,
  `e (localizedEnd a z)` equals `⟨a (e z), _⟩`. Applying `e.symm`, this
  becomes `localizedEnd a z = iota a (a (e z))`, which follows from
  `iota_intertwines` and `iota a (e z) = z`. Evaluating the subtype gives
  `S.subtype (e (localizedEnd a z)) = a (S.subtype (e z))`, which is the
  ambient linear-map equation. For uniqueness, any `e'` satisfying the
  second equation has `e'.symm.toLinearMap = e.symm.toLinearMap`, so
  `e'.symm = e.symm` and `e' = e`. Both equations are proved inside the
  unique-existence predicate exactly as stated, and the complement is
  `isCompl_ker_range`.

The closed theorem `stablePowerImageStatement` introduces `R`, `V`, `a`,
an arbitrary `n` and the three hypotheses, then applies
`stablePowerImageAt_of_stable`. No Noetherian or finite-generation
hypothesis is used.

### Item 3: `finiteActualLocalizationStatement`

From `IsNoetherianRing R`, `Module.Finite R V` and
`Module.Finite R (Localized a)`, Mathlib's
`isNoetherian_of_isNoetherianRing_of_finite` gives `IsNoetherian R V` and
`IsNoetherian R (Localized a)`. Then `noetherian_actual` gives the first
two conjuncts, and `stablePowerImageAt_of_stable` gives
`StablePowerImageAt a n` for every positive stable `n`.

### Aggregate

`actualLocalizationStabilityStatements` is the anonymous-constructor
triple of the three closed theorems, in the order of the published
conjunction.

## Scope

This module proves only the internal ordinary-unital-module aggregate. The
full possibly nonunital C.II proposition for complex algebras and their
modules remains a separate parent obligation. So do its compatible
B-linear or action lift, the finite-generation and Noetherian comparison
bridges, the power-kernel-union quotient and its comparison, and the
separate kernel and exhaustion statement task
`27b06f5a-9788-4307-b9d1-950763a472ec`. The published statement pair and
every module it imports are unchanged.
