# Constant terms along maximal block parabolics and cuspidality

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1. Worker 2 delegated cuspidality
to this task as a prerequisite of their automorphic-forms task `6c50b2fd`.
The module defines the constant terms of continuous functions on
`GL_n(K) \ GL_n(𝔸_K)` along the standard maximal block parabolics, and
cuspidality. It proves the linear and translation properties these definitions
need. No statement of the module is left unproved.

## Hypothesis: compactness of `𝔸_K / K`

Every measure-theoretic declaration takes the instance parameter
`[CompactSpace (AdeleQuotient K)]`. Here `AdeleQuotient K` is
`Adeles K ⧸ principalAdeles K` with the quotient topology, from
`Langlands.Global.AdeleQuotientStatement`. Its compactness is
`AdeleQuotientCompactStatement K`, which is stated there but not yet proved.
Once it is proved, the parameter is discharged by that proof. No other topological
hypothesis is assumed. In particular, neither Hausdorffness of `𝔸_K / K` nor
closedness of `K` in `𝔸_K` is used. Mathlib's Haar construction
`Measure.addHaarMeasure` needs only a topological additive group with its Borel
σ-algebra and a compact set with nonempty interior. Here that set is the whole
compact space `⊤`. Uniqueness of Haar measure is not used or formalized here.

No `MeasurableSpace` instance is declared on `AdeleQuotient K` or on its matrix
spaces. The measures have types `@Measure X (borel X)`, so every integral and
integrability statement below is taken for the Borel σ-algebra.

## Block unipotent matrices (`Langlands.GeneralLinear`)

`R` is any commutative ring and `a b n : ℕ`.

- `sumBlockUnipotent X`, for `X : Matrix (Fin a) (Fin b) R`, is the invertible
  block matrix `[[1, X], [0, 1]]` (Mathlib's `Matrix.fromBlocks 1 X 0 1`) indexed by
  `Fin a ⊕ Fin b`. Its stored inverse is `[[1, -X], [0, 1]]`, and both inverse laws
  are proved.
- `blockUnipotent h X`, for `h : a + b = n`, is the image of `sumBlockUnipotent X`
  in `GeneralLinear n R` under the Library's `reindex` along the standard
  consecutive numbering `finSumFinEquiv.trans (finCongr h) : Fin a ⊕ Fin b ≃ Fin n`.
  Thus the first `a` indices form the first block. `blockUnipotent_val` records its
  matrix.
- Proved properties: `blockUnipotent_zero` (`u(0) = 1`), `blockUnipotent_add`
  (`u(X + Y) = u(X) u(Y)`), `map_blockUnipotent` (compatibility with a ring
  homomorphism applied entrywise) and `continuous_blockUnipotent` (continuity
  for a topological ring, into the units topology).

So `X ↦ blockUnipotent h X` is an injective group homomorphism from the additive
group of `a × b` matrices onto the unipotent radical `N_{a,b}` of the standard upper
block parabolic `P_{a,b}` of `GL_n`, with Levi blocks `GL_a × GL_b`. The image
statement is the usual description of `N_{a,b}`; only the homomorphism and
continuity are formalized.

## Haar probability measures (`Langlands.Global`)

`K : Type u` is a number field.

- `adeleQuotientHaar K` is `Measure.addHaarMeasure ⊤` on `AdeleQuotient K` for
  the Borel σ-algebra. It is the Haar measure normalized so that the whole compact
  group has measure `1` (`adeleQuotientHaar_univ`). It is proved to be an additive
  Haar measure (`adeleQuotientHaar_isAddHaarMeasure`), and an instance records
  that it is a probability measure.
- `matrixQuotientHaar K a b` is the same construction on the compact additive group
  `Matrix (Fin a) (Fin b) (AdeleQuotient K)` of `a × b` matrices over `𝔸_K / K`.
  The instance `matrixAdeleQuotientCompactSpace` provides its compactness. The
  analogues `matrixQuotientHaar_univ`, `matrixQuotientHaar_isAddHaarMeasure` and
  the probability-measure instance are proved.
- `matrixQuotientMap X` reduces an adelic matrix modulo `K` entrywise, using the
  published quotient map `adeleQuotientMap K`. `isOpenQuotientMap_matrixQuotientMap`
  proves that it is an open quotient map. It is a finite product of the open
  quotient maps `𝔸_K → 𝔸_K / K`.
- `matrixLift X` is a chosen entrywise lift of a matrix over `𝔸_K / K`, given by
  `Function.surjInv` of the surjective quotient map.
  `matrixQuotientMap_matrixLift` proves that it is a section.
- `exists_rational_of_matrixQuotientMap_eq` proves that two adelic matrices with
  the same reduction differ by a rational matrix `C.map (diagonal K)`, with `C`
  over `K`.

The group `N_{a,b}(𝔸_K)` is identified with `Mat_{a×b}(𝔸_K)` through
`blockUnipotent`, and `N_{a,b}(K)` with `Mat_{a×b}(K)`. Hence `N_{a,b}(K) \ N_{a,b}(𝔸_K)`
is identified with `Mat_{a×b}(𝔸_K / K)`, so `matrixQuotientHaar K a b` serves as the
normalized Haar measure on `N(K) \ N(𝔸_K)`. This identification explains the
definition and is not itself formalized as a group isomorphism.

## Constant terms and cuspidality (`Langlands.Automorphic`)

The functions are the Library's `ContinuousRationalFunctions K n`
(`Langlands.Automorphic.Ambient`). These are the continuous complex functions `f` on
`AdelicGL K n = GL_n(𝔸_K)` with `f(γ x) = f(x)` for rational `γ`, with right
translation `continuousRightAction K n`. `evaluate K n f x` is `f(x)`.

- `rational_blockUnipotent` proves that the rational diagonal map
  `AdelicGL.rational K n` sends `blockUnipotent h C` to
  `blockUnipotent h (C.map (diagonal K))`.
- `constantTermIntegrand K n h f g X` is `f(u(X̃) g)`, where `X̃ = matrixLift X` and
  `u = blockUnipotent h`. `constantTermIntegrand_mk` proves that its value at
  `matrixQuotientMap Y` is `f(u(Y) g)` for every adelic lift `Y`. Two lifts differ by a
  rational `C`, `u(C + Y) = u(C) u(Y)` and `f` is left invariant under `u(C)`, so the
  chosen lift does not matter. `continuous_constantTermIntegrand` follows from this
  formula through the open quotient map. `integrable_constantTermIntegrand` follows
  because a continuous function on a compact space is integrable for a finite Haar
  measure.
- `constantTerm K n h f g` is the Bochner integral
  `∫ f(u(X) g) dX` over `Mat_{a×b}(𝔸_K / K)` against `matrixQuotientHaar K a b`. This is
  the constant term `f_N(g) = ∫_{N(K) \ N(𝔸_K)} f(n g) dn` along `N = N_{a,b}`, with
  `N(K) \ N(𝔸_K)` given total mass `1`.
- `IsCuspidal K n f` holds when `constantTerm K n h f g = 0` for all `a b : ℕ`,
  `h : a + b = n` with `0 < a` and `0 < b`, and all `g : AdelicGL K n`.
- Proved properties: `constantTerm_zero`, `constantTerm_add` and
  `constantTerm_smul` (linearity in `f`), and `constantTerm_rightAction`, which says
  that the constant term of `R(g) f` at `x` is the constant term of `f` at `x g`.
- `cuspidalSubrepresentation K n` is the subrepresentation of
  `continuousRightAction K n` whose carrier is `{f | IsCuspidal K n f}`. Closure under
  zero, addition, scalar multiplication and right translation is proved from the
  properties above.

## Original source

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
Proc. Sympos. Pure Math. 33, part 1 (1979), pp. 189–202 (literature ID
`borel-jacquet-1979-automorphic`; retained volume, PDF page = printed page − 5).

- §3.3, printed p. 194 (PDF 189): "A continuous … function on `G(A)` is cuspidal if
  `∫_{N(F)\N(A)} f(nx) dn = 0` for all … `x ∈ G(A)`, where `N` is the unipotent radical
  of any proper parabolic `F`-subgroup `P` of `G`. It suffices to check this
  condition when `P` runs through a set of representatives of the conjugacy classes
  of proper maximal parabolic `F`-subgroups."
- §4.4, printed p. 196 (PDF 191): "A cusp form is a cuspidal automorphic form."
  Automorphic forms (§4.2) are not defined in this module, so cusp forms are not
  defined here. `IsCuspidal` is the §3.3 condition. Applied to automorphic forms, it
  gives cusp forms.

Here `G = GL_n` over the number field `F = K`.

## Derived content

- **Maximal block parabolics.** The proper maximal parabolic `K`-subgroups of `GL_n`
  are, up to `GL_n(K)`-conjugacy, the standard block parabolics `P_{a,b}` with
  `a + b = n` and `a, b ≥ 1`. This is standard linear algebra: a parabolic subgroup
  is the stabilizer of a flag, and a maximal one stabilizes a single proper nonzero
  subspace. So, by Borel–Jacquet's sufficiency remark, `IsCuspidal` is their
  condition for this set of representatives. The definition quantifies over the
  representatives directly. The reduction from all proper parabolics is not
  formalized.
- **Normalization.** Borel–Jacquet integrate against an unspecified Haar measure
  `dn`. The vanishing condition does not depend on that choice. This module fixes
  the probability normalization, so `constantTerm` itself is canonical.
- **Quotient and lift.** The integral over `N(K) \ N(𝔸_K)` is realized as an integral
  over `Mat_{a×b}(𝔸_K / K)` of a function computed through a chosen lift. Lift
  independence and continuity are proved, as described above.
- **Domain.** Borel–Jacquet state the condition for continuous functions on `G(A)`.
  It is formulated here for continuous functions that are also left invariant
  under `GL_n(K)`, which is the domain where `n ↦ f(n x)` descends to
  `N(K) \ N(𝔸_K)`. The measurable ("almost all `x`") variant is not formalized.
- **Subrepresentation.** Right-translation stability of cuspidal functions is
  derived from the formula `(R(g) f)_N(x) = f_N(x g)`.

## Status

All declarations are definitions or proved lemmas under the single instance
parameter `[CompactSpace (AdeleQuotient K)]`. The additive quotient comes from
the published `Langlands.Global.AdeleQuotientStatement`; its compactness
statement remains a separate proof obligation.
