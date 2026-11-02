# Finite-length preservation by the general-linear derivatives

Author: Worker 749.

This module states that every published Bernstein–Zelevinsky derivative
`generalLinearDerivative T ψ N k hk` of
`Langlands.Representation.Derivative.Iteration` sends a smooth representation
of finite length to a smooth representation of finite length. It has one
Prop-valued definition, the principal proposition
`Langlands.Derivative.GeneralLinearDerivativeFiniteLengthStatement.{uF, uV} F T`.
This proposition definition supplies no proof. It proves nothing and
constructs no functor. Finite length of the derivatives remains a proof
obligation.

## The principal proposition

The parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with level parameters in the order `uF, uV`. The
carrier universe `uV` is independent of `uF`. The body installs
`letI := T.topology`, so all groups carry the topology supplied by `T`. No
canonical topology is substituted and `F` is not made canonical. The Lean body
is

```
∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N)
  (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)),
  A.HasFiniteLength →
    ((generalLinearDerivative.{uF, uV} T ψ N k hk).obj A).HasFiniteLength
```

Here `ψ` has the type `@UnitaryAdditiveCharacter F.Carrier _ T.topology`. The
functor `generalLinearDerivative T ψ N k hk` goes from
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)` to
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N - k) F.Carrier)`. Input and output
carriers stay in `Type uV`; `uV` is not replaced by `max uF uV` or fixed to a
particular universe.

### What finite length means

`SmoothRep.HasFiniteLength` is the published definition of
`Langlands.Representation.Category.Basic`:

```
def HasFiniteLength (A : SmoothRep R G) : Prop :=
  IsFiniteLength R[G] A.representation.asModule
```

So it is Mathlib's `IsFiniteLength` for the actual carrier, viewed as a module
over the complex group algebra `MonoidAlgebra ℂ G` through the representation.
It is finite composition length over the group algebra, not finite dimension
over `ℂ`. Unfolded, the proposition says: for every `ψ`, `N`, `k`,
`hk : k ≤ N` and `A`,

```
IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear N F.Carrier))
    A.representation.asModule →
  IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (N - k) F.Carrier))
    ((generalLinearDerivative T ψ N k hk).obj A).representation.asModule
```

On the left the group algebra of `GL_N` acts through `A`. On the right the
group algebra of `GL_(N-k)` acts through the actual `GL_(N-k)` action of the
derivative object, described below. Every `ℂ[G]`-submodule of a smooth
representation is again smooth, so for smooth representations this length
is the length in the smooth category, which is the length used by the source.
The Lean statement does not depend on this remark.

During development the proposition was checked to be definitionally equal
(`Iff.rfl`) to three forms: the body above with `ψ` written with the explicit
topology `@UnitaryAdditiveCharacter F.Carrier _ T.topology`; the unfolded
group-algebra form above; and

```
∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N),
  SmoothRep.PreservesFiniteLength (generalLinearDerivative T ψ N k hk)
```

with the published predicate `SmoothRep.PreservesFiniteLength` of
`Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor`. That
predicate unfolds to the same quantification over `A` with no extra
hypothesis. The module states the direct form so that it imports only
`Iteration`.

### What is not assumed or changed

The proposition concerns the objects `(generalLinearDerivative T ψ N k hk).obj A`
of the named published functor, with their actual carriers and actual
`GL_(N-k)` actions. It adds no hypothesis on `A` other than finite length. In
particular it does not assume that `A` is irreducible, unitary, cuspidal or
admissible, and it does not assume that the derivative is nonzero. A zero
derivative has length zero and counts as finite length. No exactness,
Leibniz, cuspidal-derivative or classification result is a premise.

The conclusion is finite length over the group algebra of `GL_(N-k)`. It is
not finite dimensionality, not finite length after restriction to a subgroup
or to a smaller carrier, not an identity in a Grothendieck group and not a
statement about a replacement derivative functor.

## The functors covered

The published construction fixes what `D = generalLinearDerivative T ψ N k hk`
is:

- `k = 0`: `generalLinearDerivative T ψ N 0 hk` is the identity functor of
  `SmoothRep ℂ (GeneralLinear N F.Carrier)` (`generalLinearDerivative_zero`).
  This is the source's `π^(0) = π`. For `k = 0` the proposition is trivially
  true.
- `k + 1 ≤ N`: write `n = N - (k + 1)`. Then
  `generalLinearDerivative T ψ N (k + 1) hk` is
  `generalLinearRankCast T (rank_eq_of_succ_le hk) ⋙ generalLinearDerivativePositive T ψ n k`
  (`generalLinearDerivative_succ`), and
  `generalLinearDerivativePositive T ψ n k` is
  `generalLinearRestriction T (n + k) ⋙ phiMinusIterate T ψ n k ⋙ Mirabolic.psiMinus T n`
  (`generalLinearDerivativePositive_eq_comp`).

The complete telescope for order `k + 1` is therefore

```
GL_N  --rank cast-->  GL_(n+k+1)  --Res-->  P_(n+k+1)
      --Φ⁻-->  P_(n+k)  --Φ⁻-->  …  --Φ⁻-->  P_(n+1)  --Ψ⁻-->  GL_n
```

with `k` steps of `Φ⁻`. Each step is as follows.

- The rank cast `generalLinearRankCast T (rank_eq_of_succ_le hk)` is `Eq.rec`
  of the identity functor along `N = N - (k + 1) + k + 1`. On objects it is
  the cast along this equality of categories (`generalLinearRankCast_obj`). On
  morphisms it is heterogeneously equal to the identity
  (`generalLinearRankCast_map_heq`). It is internal packaging, not a source
  construction.
- `generalLinearRestriction T (n + k)` restricts a representation of
  `GL_(n+k+1)` to the mirabolic subgroup `P_(n+k+1) = mirabolic (n + k)`. It
  keeps the carrier and the underlying linear maps.
- `phiMinusIterate T ψ n k` is `(Φ⁻)^k : P_(n+k+1) → P_(n+1)`, applying
  `Mirabolic.phiMinus T ψ (n + j)` at the largest rank first
  (`phiMinusIterate_succ`). Each `Mirabolic.phiMinus` takes the coinvariant
  quotient for the unipotent radical of the mirabolic group with the
  character `θ_ψ` built from `ψ`, and twists the descended action of
  `P_(m+1)` by `|det|^(-1/2)`, where `m + 1` is the rank of the output.
- `Mirabolic.psiMinus T n : P_(n+1) → GL_n` takes the coinvariant quotient for
  the same radical with the trivial character and twists the descended
  `GL_n` action by `|det|^(-1/2)`.

The output object `D.obj A` has as carrier the actual `Ψ⁻` coinvariant
quotient `Coinvariants _ (radical n F.Carrier) 1` of the `(Φ⁻)^k` output
(`psiMinus_obj_carrier`). The group `GL_n = GL_(N-(k+1))` acts by
`g • q(v) = |det g|^(-1/2) q(levi g • v)` (`psiMinus_action`), where `q` is
the quotient map and `levi g` is the image of `g` in `P_(n+1)`. This is the
`GL_(N-k)` action whose group-algebra module the conclusion measures. No
target cast is applied: the target rank of `generalLinearDerivativePositive`
is `n = N - (k + 1)` itself.

The character `ψ` enters `D` only through `Φ⁻`. For `k ≤ 1` there is no `Φ⁻`
step.

## Boundary cases

All ranks and orders with `k ≤ N` are included:

- `N = 0`: only `k = 0`, the identity functor of
  `SmoothRep ℂ (GeneralLinear 0 F.Carrier)` (`generalLinearDerivative_zero_zero`).
- `k = 0`, any `N`: the identity functor.
- `N = 1`: `k = 0` gives the identity (`generalLinearDerivative_one_zero`).
  `k = 1` gives `generalLinearRestriction T 0 ⋙ Mirabolic.psiMinus T 0`, the
  functor `GL_1 → P_1 → GL_0` (`generalLinearDerivative_one_one`). Its output is
  a representation of the trivial group `GL_0`, whose group algebra is isomorphic to `ℂ`, so
  for this case finite length is finite dimensionality of the `Ψ⁻`
  coinvariant space.
- `k = N`: the functor has target `GL_(N - N)` as published. The statement is
  about this functor itself. It does not compose with the extra cast
  `Nat.sub_self N` used by the published top equations
  (`generalLinearDerivative_top`).

Orders `k > N` are not covered, since the published wrapper requires
`hk : k ≤ N`. `UnitaryAdditiveCharacter` bundles continuity for `T.topology`
and nontriviality, so the statement says nothing about the trivial additive
character.

## Source and provenance

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Page
numbers below are printed numbers, with one-based PDF pages in parentheses.

- §3.5, printed p.452 (PDF page 13): for `τ ∈ Alg P_n`,
  `τ^(k) = Ψ⁻ ∘ (Φ⁻)^(k-1)(τ) ∈ Alg G_(n-k)` for `k = 1, …, n`.
- §4.3, printed p.454 (PDF page 15): for `π ∈ Alg G_n`, `π^(0) = π` and
  `π^(k) = (π|_(P_n))^(k)` for `k = 1, …, n`.
- §4.4, printed p.454 (PDF page 15), the theorem of Gelfand and Kazhdan: if
  `π ∈ Alg G_n` is quasicuspidal then `π^(k) = 0` for `0 < k < n`, and if `π`
  is cuspidal and irreducible then `π^(n) = 1` is one-dimensional.
- §4.1, printed p.453 (PDF page 14): every irreducible `ω` lies in the
  Jordan–Hölder set of a product `ρ_1 × … × ρ_r` of irreducible cuspidal
  representations, and with a suitable ordering of its support `ω` embeds
  into that product (referring to 2.5, 2.7 and 2.9).
- Lemma 4.5, printed p.455 (PDF page 16): for `ρ ∈ Alg G_m`, `ω ∈ Alg G_l` and
  `π = ρ × ω`, each `π^(k)` is glued from the products `ρ^(i) × ω^(k-i)`,
  `i = 0, …, k`. It is proved in 4.14; Corollary 4.14(c), printed p.458
  (PDF page 19), is the general Leibniz filtration.

No applicable errata entry was found in the central library, the literature
index or the public notes.

### What the source asserts

The source defines the derivatives and states the ingredients above. It does
not state finite-length preservation by `π ↦ π^(k)` as a numbered assertion.
The only use of finite length found in the source is in §4.5, printed p.455
(PDF page 16), after Lemma 4.5. There `ℛ_n` is the Grothendieck group of
algebraic `G_n`-modules of finite length, and for `π ∈ Alg G_n` of finite
length the source sets `𝒟π = Σ_k π^(k) ∈ ℛ`. This tacitly presupposes that
every `π^(k)` has finite length, and Corollary 4.6 and the proof of
Theorem 4.2 in §4.7 use it. No proof of that presupposition was found in the
pages read or by a text search of the extracted text of the whole PDF.

### Derived provenance

The statement is an internally derived general finiteness assertion for the
published derivative functors. It makes explicit the presupposition of §4.5
for all finite-length inputs and all orders `k ≤ N`. It is not a quotation of
a numbered assertion of the source. The source ingredients above (definitions,
cuspidal derivatives, embedding into cuspidal products, Leibniz gluing) are
the expected tools of a proof, not this conclusion.

The Library normalizes `Ψ⁻` and `Φ⁻` by the fixed determinant twists
`|det|^(-1/2)`, where the source uses `mod_V^(-1/2)`. A twist by a character
of the group acting changes neither the carrier nor the lattice of
invariant subspaces, so finite length does not depend on the normalization.
No Haar-modulus comparison is needed for this statement.

The formulation through `SmoothRep.HasFiniteLength`, the quantification of
`ψ`, `N`, `k`, `hk` and `A` in one proposition, and the use of the direct form
instead of `PreservesFiniteLength` are internal choices that follow the task
contract.

## Remaining proof obligation

A proof of `GeneralLinearDerivativeFiniteLengthStatement F T` must show, for
every `ψ`, every `N`, every `k ≤ N` and every finite-length `A`, that
`(generalLinearDerivative T ψ N k hk).obj A` has finite length, with no added
hypothesis. Finite length of `A` and exactness of the derivative alone do not
give this: exactness transports a composition series of `A` to a filtration
of the derivative, but finite length of the derivatives of the irreducible
factors still has to be shown.

One possible route, recorded only as a suggestion: embed an irreducible input
into a finite product of cuspidal representations (§4.1); apply exactness to
the injection; bound the derivative of the product by the Leibniz filtration,
cuspidal vanishing and the finiteness of top cuspidal derivatives (§4.4);
then use finite-length preservation by normalized products and closure of
finite length under extensions and subobjects; finally extend to all
finite-length inputs by a composition series and exactness. Such a proof
needs actual induction over finite products, carrier transports along rank
equalities and the rank-zero cases. This route is not an accepted proof and
is not required.

## Imports and independence

The module imports only `Langlands.Representation.Derivative.Iteration`, for
the derivative functors. `SmoothRep.HasFiniteLength` comes in through it from
`Langlands.Representation.Category.Basic`. No proof module is imported. The
`Langlands` import closure of the module, not counting the module itself, has
52 modules: `Iteration`, `MirabolicMinus`, `MirabolicCharacter`, and modules
on groups (`Group.GL`), local fields, topology, smooth representations and
their transfer, admissibility cofinality, twists, coinvariants and
localization, matrix coefficients and Whittaker characters.
`Representation/Dual/Definitions` in the closure only builds algebraic dual
maps of intertwiners; it is not a duality theorem. The closure contains no
classification, segment, multisegment, square-integrable, tempered, socle,
cuspidal-support, parabolic-induction, Jacquet-formula, irreducibility,
exactness, Leibniz-filtration or plus-functor module.

Neither the module nor its closure uses the special-head product criterion of
task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
`SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`, or
any result of the excluded multisegment exhaustion, strong-head existence,
quotient coverage, ordered conversion, tempered uniqueness, square-integrable,
regular or socle exhaustion, analytic segment classification, special-segment
square-integrability, segment-socle irreducibility, unlinked or linked socle
structure, socle commutation, linked socle gluing or ordered socle existence
tasks. It uses no result of Zelevinsky 1980, in particular none of its
segment derivative formulas, and nothing from task
`8e5b4563-0365-41c7-b134-70f2a0b36292`. These exclusions apply to every proof
of this statement and to all of its prerequisites.
