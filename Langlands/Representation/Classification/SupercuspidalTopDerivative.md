# The top derivative of a supercuspidal representation

Author: Worker 818.

This module proves two unconditional facts about the top derivative
`Ψ⁻ (Φ⁻)^n (A|P)` of a smooth complex representation `A` of `GL_(n+1)`, for
the actual published derivative functors. Both are ingredients of BZ77 §4.4.

1. **Whittaker equivariance of the top quotient.** The composite quotient map
   `topQuotient T ψ n A : A → Ψ⁻ (Φ⁻)^n (A|P)` is surjective. It transforms
   under the upper unipotent group by the published standard Whittaker
   character. So every linear functional on the top derivative pulls back to a
   standard Whittaker functional on `A`, an element of the published
   `Whittaker.glFunctionals`.
2. **Nonvanishing.** If `A` is nonzero and satisfies the published
   `GeneralLinear.IsSupercuspidal`, then the derivative of order `n + 1`,
   `Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl` of `A`, is
   nonzero (`nontrivial_generalLinearDerivative_top`).

The module has no hypotheses beyond those stated in each declaration. In
particular it does not assume Whittaker multiplicity one and does not import
`Whittaker.MultiplicityOneStatement`. It does not prove the target proposition
`Langlands.Classification.SupercuspidalDerivatives`, whose top-derivative
clause is the equality `finrank = 1`. It is an internal unit of task
`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`. The final proof of that task combines
part 1 with the published proof of multiplicity one to get `finrank ≤ 1`, and
part 2 to get `finrank ≥ 1`.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- §4.4, printed p.454 (one-based PDF page 15), Theorem (Gelfand–Kazhdan),
  second sentence: "If π is cuspidal and irreducible, then π^(n) = 1 is a
  one-dimensional representation." The source gives no proof. It refers to
  Gelfand–Kazhdan ([1], chap. III).
- §4.3, printed p.454, and §3.5, printed p.452: the derivatives are
  `π^(k) = Ψ⁻ (Φ⁻)^(k-1) (π|_(P_n))`.

The source states the result without proof, so the two facts proved here and
their Lean arguments were written for this module. The source's "cuspidal" is
represented by the published `IsSupercuspidal`. It is used only through
unit 1 of this task: the vanishing of the intermediate derivatives and the
rank transport `isSupercuspidal_rankCast`. No
errata entry for BZ77 is registered in the project literature index, the
central library or the public notes.

## Parameters and normalization

Throughout, `p` is prime, `F : PadicField.{uF} p` is implicit, and
`T : F.TopologicalData` is explicit. Every statement installs
`letI := T.topology`. The character is
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`. Representations live in
`SmoothRep.{0, uF, uV} ℂ _`, with the carrier universe `uV` independent of
`uF`. The derivatives are the published `Derivative.generalLinearDerivative`
and `Derivative.generalLinearDerivativePositive`, used unchanged with their
determinant `|det|^(-1/2)` normalization. The normalizing character of `Φ⁻`
is `1` on upper unipotent elements (`phiMinusCharacter_eq_one_of_upper`), so it
does not appear in the Whittaker character.

## Declarations

All declarations are in the namespace
`Langlands.Classification.SupercuspidalTopDerivative`. Line numbers refer to
`SupercuspidalTopDerivative.lean`.

### Upper unipotent mirabolic elements (ll.30–94, any commutative ring `R`)

- `exists_radical_mul_successor_upper` (l.39): an upper unipotent element `g`
  of `mirabolic (n + 1) R` (inside `GL_(n+2)`) factors as
  `radicalElement c * successor g'`. Here `c i = g (castSucc i) (last)` is the
  last column of `g` above the diagonal, `g'` is upper unipotent in
  `mirabolic n R`, and `g'` has the same upper-left `(n+1) × (n+1)` entries
  as `g`. The proof multiplies by `radicalElement (-c)` and applies
  `exists_successor_eq` from the published vanishing module.

Triviality of `mirabolic 0 R` (inside `GL_1`) is reused from the existing
`Langlands.GeneralLinear.Mirabolic.rankOne_eq_one` in `Langlands.Group.GL.Mirabolic`.

### Whittaker equivariance of the top quotient (ll.96–242)

- `phiMinusCharacter_eq_one_of_upper` (l.101): the `Φ⁻` normalizing character
  `|det|^(-1/2)` on the mirabolic group is `1` on upper unipotent elements.
- `phiMinusQuotient_eq_of_eq_radical_mul_successor` (l.117): if
  `g = radicalElement c * successor g'` with `g'` upper unipotent, then
  `phiMinusQuotient (g • w) = ψ(c (last n)) • (g' • phiMinusQuotient w)`. This
  combines the published `phiMinusQuotient_radical`, `phiMinus_action` and
  `theta_radicalElement`.
- `psiMinusQuotient_iterateQuotient_upper` (l.142): for `X` a smooth
  representation of `mirabolic (0 + j)` and `u` in it upper unipotent, the
  composite `X → Ψ⁻ (Φ⁻)^j X` (the published `iterateQuotient` followed by
  `psiMinusQuotient`) sends `u • v` to `θ_j(u) •` (image of `v`), where
  `θ_j` is the published `Whittaker.standardCharacter ψ (0 + j)`, that is,
  `u ↦ ψ(Σ_i u_(i, i+1))`. The proof is by induction on `j`. For `j = 0` the
  group is trivial, so `u` lies in the radical and the character is `1`. For
  `j + 1`, the factorization above contributes `ψ(u_(j, j+1))`, and the
  induction hypothesis for `g'` contributes the remaining superdiagonal
  entries. The declaration uses `set_option maxHeartbeats 400000` (l.139).
- `topQuotient T ψ n A` (l.207): the composite linear map
  `A → (generalLinearDerivativePositive T ψ 0 n).obj A`, i.e. onto
  `Ψ⁻ (Φ⁻)^n (A|P)`, from `GL_(0+n+1)` to `GL_0`. It is the published
  `iterateQuotient` followed by the published `psiMinusQuotient`.
- `topQuotient_surjective` (l.216): it is surjective.
- `comp_topQuotient_mem_glFunctionals` (l.226): for every linear functional
  `f` on the top derivative, `f ∘ topQuotient` lies in the published
  `Whittaker.glFunctionals ψ (0 + n) A.representation`.

Only this direction is proved. The module does not identify the kernel of
`topQuotient`, so it does not show that the top derivative is the space of
twisted coinvariants of the upper unipotent group.

### Nonvanishing of the top derivative (ll.244–384)

- `nontrivial_of_isIrreducible` (l.247): an irreducible representation is
  nonzero.
- `phiMinus_obj_heq`, `phiMinusIterate_obj_succ_bottom`,
  `generalLinearRestriction_rankCast_heq`, `nontrivial_rankCast`,
  `isIrreducible_rankCast` (ll.252–307): rank bookkeeping.
  `phiMinusIterate_obj_succ_bottom` (l.265) shows that
  `(phiMinusIterate T ψ m (j + 1)).obj Y` equals
  `(phiMinus T ψ m).obj ((phiMinusIterate T ψ (m + 1) j).obj Y')` whenever `Y`
  and `Y'` are the same object at the ranks `m + (j + 1)` and `m + 1 + j`
  (stated with `HEq`). The others show that the published rank transport
  `generalLinearRankCast` preserves restriction, nontriviality and
  irreducibility.
- `nontrivial_phiMinusIterate` (l.310): for every supercuspidal nonzero `A` of
  `GL_(m+j+1)`, `(Φ⁻)^j (A|P)` is nonzero. The proof is by induction on `j`.
  For `j + 1`, write `(Φ⁻)^(j+1)` as `Φ⁻` at rank `m` after `(Φ⁻)^j` down to
  rank `m + 1`. The induction hypothesis makes `Z = (Φ⁻)^j (A|P)` nonzero. Its
  `Ψ⁻` is the derivative `generalLinearDerivativePositive T ψ (m + 1) j` of
  `A`, which is zero by the published
  `subsingleton_generalLinearDerivativePositive` (`m + 1 > 0`). The published
  lemma `Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus` (module
  `Derivative.MinusVanishing`, Worker 1025) says that a smooth representation
  of `mirabolic (m + 1)` with zero `Ψ⁻` and zero `Φ⁻` is zero. So `Φ⁻ Z` is
  nonzero.
- `psiMinusQuotient_zero_injective` (l.340): `Ψ⁻` at `P_1` is injective,
  because its kernel is spanned by `u • v - v` for `u` in the trivial group.
- `nontrivial_generalLinearDerivativePositive_top` (l.356): the top derivative
  `generalLinearDerivativePositive T ψ 0 n` of a nonzero supercuspidal
  `A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier)` is
  nonzero.
- `nontrivial_generalLinearDerivative_top` (l.369): BZ77 §4.4, nonvanishing
  half. For every nonzero
  `A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)` with
  `IsSupercuspidal A.representation`,
  `(Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A` is
  nonzero. By definition, the published `generalLinearDerivative` at order
  `n + 1` is `generalLinearRankCast T (rank_eq_of_succ_le le_rfl) ⋙
  generalLinearDerivativePositive T ψ ((n + 1) - (n + 1)) n`. The proof
  replaces the rank `(n + 1) - (n + 1)` by a variable `m` with `m = 0`,
  substitutes, and applies the previous result to the rank-cast
  representation, which is still nonzero and supercuspidal.

## Dependency audit

The module imports
`Langlands.Representation.Classification.SupercuspidalDerivativeVanishing`
(published, unit 1 of this task),
`Langlands.Representation.Derivative.MinusVanishing` (published, Worker 1025,
unit 2 of this task) and `Langlands.Representation.Whittaker.GeneralLinear`
(published standard Whittaker character and `glFunctionals`). Its Library
import closure has 81 modules. It contains no segment, socle, head,
multisegment, Langlands-classification, square-integrability, tempered,
product-irreducibility, Leibniz/filtration, Whittaker multiplicity-one,
Shalika, Gelfand–Kazhdan, Whittaker-finiteness or coinvariant-finiteness
module. The only `Classification` modules in it are the definition module
`Classification.Supercuspidal` and unit 1.

The mathematical inputs used are the derivative functors and their quotient
maps (`MirabolicMinus`, `Iteration`), the mirabolic radical and successor
embedding, the published standard Whittaker character and `glFunctionals`,
`IsSupercuspidal`, the published vanishing of intermediate derivatives
(unit 1) and the joint vanishing lemma `subsingleton_of_psiMinus_phiMinus`
(unit 2).

## Scope

- Nothing is claimed about the dimension of the top derivative. Its
  finiteness and the bound `finrank ≤ 1` need Whittaker multiplicity one and
  are left to the final proof of the task.
- The nonvanishing results assume `Nontrivial A`, not irreducibility.
  `nontrivial_of_isIrreducible` converts irreducibility to this hypothesis.
  `IsSupercuspidal` enters only through
  `subsingleton_generalLinearDerivativePositive` at orders `m + 1 > 0` and
  through `isSupercuspidal_rankCast`.
- The equivariance results hold for every smooth representation of
  `GL_(0+n+1)`. They need no supercuspidality.
