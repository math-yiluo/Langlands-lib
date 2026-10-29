# Vanishing of the intermediate derivatives of a supercuspidal representation

Author: Worker 818.

This module proves the vanishing half of BZ77 §4.4 for the actual published
derivative functors. Let `A` be a smooth complex representation of `GL_N`
that satisfies the published predicate `GeneralLinear.IsSupercuspidal`. Then
for every `0 < k < N`, the derivative
`Derivative.generalLinearDerivative T ψ N k hk` of `A` is zero, stated in Lean
as `Subsingleton`. Irreducibility and admissibility are not used. The module
says nothing about the top derivative `k = N`.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- §4.4, printed p.454 (one-based PDF page 15): "Let π ∈ Alg G_n be
  quasicuspidal. Then π^(k) = 0 for 0 < k < n." The source gives no proof. It
  refers to Gelfand–Kazhdan ([1], chap. III).
- §4.3, printed p.454, and §3.5, printed p.452: the derivatives are
  `π^(k) = Ψ⁻ (Φ⁻)^(k-1) (π|_(P_n))`.

The Lean proof is a direct argument written for this module, described below.
The source's premise "quasicuspidal" means that every proper Jacquet module
vanishes. The Lean statement uses the published `IsSupercuspidal`. That
predicate is stronger (it adds admissibility), and the proof uses only one of
its Jacquet-vanishing clauses. No errata entry for BZ77 is registered in the
project literature index, the central library or the public notes.

## Parameters and normalization

Throughout, `p` is prime, `F : PadicField.{uF} p` is implicit, and
`T : F.TopologicalData` is explicit. Every statement installs
`letI := T.topology`; no canonical topology is used. The character is
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`. Representations live in
`SmoothRep.{0, uF, uV} ℂ _`, with the carrier universe `uV` independent of
`uF`. The derivative is the published `Derivative.generalLinearDerivative`,
with its determinant `|det|^(-1/2)` normalization, used unchanged. The
normalization does not matter here, because every normalizing character used
in the proof takes the value `1` (see `phiMinusCharacter_eq_one`).

## Declarations

All declarations are in the namespace
`Langlands.Classification.SupercuspidalDerivativeVanishing`. Line numbers refer to
`SupercuspidalDerivativeVanishing.lean`.

### Block unipotent matrices (ll.25–221, any commutative ring `R`)

- `IsBlockUnipotent m g` (l.33): every entry of `g` in one of the first `m`
  columns or in a row of index `≥ m` equals the identity entry. In block
  form, `g = [[I_m, Y], [0, I]]`.
- `mem_upperUnipotent_of_isBlockUnipotent` (l.37): such a `g` lies in
  `GeneralLinear.upperUnipotent N R`.
- `mem_mirabolic_of_isBlockUnipotent` (l.50): for `m ≤ n`, such a `g` in
  `GL_(n+1)` lies in `mirabolic n R`, because its last row is standard.
- `mem_radical_of_isBlockUnipotent` (l.60): an element of `mirabolic m R`
  (inside `GL_(m+1)`) that is block unipotent for `m` lies in `radical m R`.
- `isBlockUnipotent_of_mem_binary` (l.67): every element of the unipotent
  radical of the published two-block shape `BlockShape.binary m c` is block
  unipotent for `m`.
- `binary_parabolic_ne_top` (l.112): for a nontrivial ring and `m, c > 0`, the
  parabolic of `BlockShape.binary m c` is proper. The witness is the
  permutation matrix of the transposition of indices `m` and `0`. It has a
  nonzero entry below the block diagonal.
- `exists_successor_eq` (l.130): an element `s` of `mirabolic (n+1) R` whose
  last column vanishes above the diagonal and whose row `n` is the standard
  row on the first `n + 1` columns is `successor h` for an `h` in
  `mirabolic n R`. Here `h` is the top-left `(n+1) × (n+1)` block, and its
  inverse is the corresponding block of `s⁻¹`.
- `exists_radical_mul_successor` (l.174): for `m ≤ n`, a block unipotent
  element `g` of `mirabolic (n+1) R` factors as
  `radicalElement c * successor g'`. Here `g'` is block unipotent for `m`, and
  the last coordinate `c (Fin.last n)` is `0`. The vector `c` is the last
  column of `g` above the diagonal. Its last coordinate is `0` because row `n`
  of `g` is standard (`m ≤ n`).

### The iterated quotient (ll.223–302)

- `iterateQuotient T ψ m j X` (l.228): the composite of the published quotient
  maps `phiMinusQuotient`, as a linear map
  `X → (phiMinusIterate T ψ m j).obj X`. It applies the largest-rank step
  first, matching the recursion of `phiMinusIterate`.
- `iterateQuotient_surjective` (l.237): this map is surjective.
- `phiMinusCharacter_eq_one` (l.249): the `Φ⁻` normalizing character
  `|det|^(-1/2)` restricted to the mirabolic group is `1` on block unipotent
  elements, since their determinant is `1`.
- `psiMinusQuotient_iterateQuotient_invariant` (l.266): for `X` a smooth
  representation of `P_(m+j+1)` (that is, `mirabolic (m + j)`) and `g` a block
  unipotent element of it for `m`,
  `psiMinusQuotient (iterateQuotient X (g • v)) = psiMinusQuotient (iterateQuotient X v)`.
  The proof is by induction on `j`. For `j = 0`, `g` lies in the radical and
  `psiMinusQuotient_radical` applies. For `j + 1`, write
  `g = radicalElement c * successor g'` (`exists_radical_mul_successor`). The
  published `phiMinusQuotient_radical` turns the radical factor into the
  scalar `θ(radicalElement c) = ψ(c (Fin.last _)) = ψ(0) = 1`. The published
  `phiMinus_action` turns the action of `successor g'` into the action of
  `g'` on `Φ⁻ X`, up to the normalizing character, which is `1` by
  `phiMinusCharacter_eq_one`. The induction hypothesis for `Φ⁻ X` and `g'`
  then applies.

### Vanishing (ll.304–367)

- `subsingleton_generalLinearDerivativePositive` (l.308): for `m > 0`, every
  supercuspidal `A` of `GL_(m+j+1)` has zero
  `generalLinearDerivativePositive T ψ m j`. The composite
  `A → Ψ⁻ (Φ⁻)^j (A|P)` is a surjective linear map. By the previous lemma it
  is invariant under the unipotent radical of `BlockShape.binary m (j+1)`, as
  every element of that radical is block unipotent for `m` and lies in the
  mirabolic group. Hence the composite factors through the published
  coinvariants `Jacquet.Coinvariants A.representation (B.conjugateUnipotent 1)`
  via `Jacquet.lift`. Those coinvariants are zero by the Jacquet clause of
  `IsSupercuspidal` for the proper parabolic of `B` (`binary_parabolic_ne_top`)
  at `g = 1`. So the derivative is zero.
- `isSupercuspidal_rankCast` (l.343): the published rank transport
  `generalLinearRankCast` preserves `IsSupercuspidal`.
- `subsingleton_generalLinearDerivative` (l.354): the main result. For
  `k ≤ N`, `0 < k` and `k < N`, every supercuspidal `A` of `GL_N` has
  `Subsingleton ((Derivative.generalLinearDerivative T ψ N k hk).obj A)`. It
  rewrites with the published `generalLinearDerivative_of_pos` and applies the
  previous two results with `m = N - k > 0` and `j = k - 1`.

## Dependency audit

The module imports `Langlands.Representation.Classification.Supercuspidal`,
`Langlands.Representation.Derivative.Iteration`,
`Langlands.Group.GL.MirabolicOppositeIntersection` and
`Langlands.Group.GL.Maps`. Their transitive `Langlands` import closure has
60 modules. It consists of the `Group.GL` matrix and block-shape modules, the
`LocalField` normalization modules, `HarmonicAnalysis.Basic`, and the
`Representation` modules `Category`, `Dual.Definitions`, `Jacquet`
(coinvariants, localization, smooth twist), `MatrixCoefficient`, `Smooth`,
`Twist`, `Unitary.Basic`, `Whittaker.Algebraic`, `Whittaker.GeneralLinear`,
`Classification.Supercuspidal`, and `Derivative.{MirabolicCharacter,
MirabolicMinus, Iteration}`. It contains no segment, socle, head,
multisegment, Langlands-classification, square-integrability, tempered,
product-irreducibility, Leibniz/filtration, Whittaker-finiteness or
coinvariant-finiteness module.

The mathematical inputs actually used are the definitions of the derivative
functors and their quotient maps (`MirabolicMinus`, `Iteration`), the
mirabolic radical (`MirabolicRadical`), the published block shapes and
`IsSupercuspidal`, and the coinvariant lift `Jacquet.lift`. None of the
excluded results of task `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` is used,
directly or transitively. In particular, no segment derivative formula,
socle/head existence, Jacquet formula, classification or exhaustion theorem,
product irreducibility criterion, finiteness statement, multiplicity-one
statement or Leibniz filtration is used.

## Scope

- Only the intermediate orders `0 < k < N` are treated. Nothing is claimed
  about `k = 0` or the top derivative `k = N`.
- The hypothesis is the published `IsSupercuspidal`. Only its clause for the
  proper parabolic of `BlockShape.binary (N - k) k`, at the identity
  conjugate, is used.
