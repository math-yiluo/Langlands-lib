# Uniform small-coordinate dilation for actual JPS function spaces (statement)

Author: Worker 941. This unit states the small-coordinate dilation step in the
proof of JPS (1979), Lemma (2.2.1), printed p.182. It uses the actual function
spaces, coordinate actions and coordinate-germ quotients published in
`Langlands.Representation.Whittaker.JPSFunctionSpace`. It is a proposition
definition only. Nothing here proves the assertion, and no proof of it is
claimed.

## Declaration

`Langlands.Whittaker.JPSUniformDilationStatement.{uF} : Prop`, in module
`Langlands.Representation.Whittaker.JPSUniformDilationStatement`. The module
imports only `Langlands.Representation.Whittaker.JPSFunctionSpace` and opens
the namespace `Langlands.Whittaker.JPSFunctionSpace`. Its only universe
parameter is the unrestricted field universe `uF`. The proposition is, in this
exact order:

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  letI := T.topology
  ∀ (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
    IsLocallyConstantSpace W T →
    HasFiniteCoordinateOperatorSpan W T i →
    ∃ (Y : Finset (F.Carrierˣ → ℂ))
      (A : (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule),
      (∀ η ∈ Y, Continuous η ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) ∧
      (∀ η ∈ Y, A η ∈ Submodule.span ℂ {B : Module.End ℂ W.toSubmodule |
        ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧
          coordinateRepresentation W i b = B}) ∧
      (∀ (b : F.Carrierˣ) (f : W.toSubmodule),
        sigma W T i b (germMap W T i f) =
          germMap W T i (∑ η ∈ Y, η b • A η f)) ∧
      ∀ f : W.toSubmodule,
        ∃ ε : ℝ, 0 < ε ∧
          ∀ a : Torus F n,
            T.normalizedAbs (a i : F.Carrier) < ε →
            ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
              (coordinateRepresentation W i b f).val a =
                ∑ η ∈ Y, η b * (A η f).val a
```

## Quantifiers

The prime `p`, the field `F`, the topological data `T`, the rank `n : ℕ`
(zero included), the space `W` and the coordinate `i : Fin n` are universally
quantified. At `n = 0` the type `Fin 0` is empty, so the statement holds
vacuously at rank zero. Rank zero is not excluded by any hypothesis.

The only two hypotheses are the published `IsLocallyConstantSpace W T` and
`HasFiniteCoordinateOperatorSpan W T i`. Then the finite set `Y` and the total
operator family `A` are chosen. Both come before every `b` and every `f`. So
one finite family of functions and one family of operators on `W` serve every
function in `W`.

The four conclusions are:

1. *Finite functions.* Every `η ∈ Y` is continuous on `F.Carrierˣ`, and the
   complex span of its translates `a ↦ η (b * a)`, `b ∈ F.Carrierˣ`, is
   finite-dimensional. The functions `η` need not be characters or sums of
   characters.
2. *Bounded operators.* Every `A η` with `η ∈ Y` lies in the complex span
   `S₊` of the actual coordinate dilations `coordinateRepresentation W i b`
   with `T.normalizedAbs (b : F.Carrier) ≤ 1`. These are endomorphisms of `W`
   itself, not of the quotient. A finite combination of such dilations is
   fixed once and applied to every `f`.
3. *Quotient identity for all `b`.* For every `b ∈ F.Carrierˣ`, without a
   restriction on `|b|`, and every `f`, the germ of `ρ_i(b) f` equals the germ
   of `∑_{η ∈ Y} η(b) A_η f` in the actual quotient `CoordinateGerm W T i`.
4. *Uniform pointwise identity.* For every `f` there is one `ε > 0` such that,
   for every torus tuple `a` with `|a_i| < ε` and every `b` with `|b| ≤ 1`,
   `f (a · e_i(b)) = ∑_{η ∈ Y} η(b) (A_η f)(a)`. The left side is
   `(coordinateRepresentation W i b f).val a`.

Clause 4 has the exact pattern
`∀ f, ∃ ε > 0, ∀ a, |a_i| < ε → ∀ b, |b| ≤ 1 → …`. The threshold may depend
on `f`. It must precede the whole tuple `a`, including all coordinates other
than `i`, and every admissible `b`. A threshold chosen separately for each `b`
or for each tuple of other coordinates does not suffice.

Clause 3 is the germ identity for every `b`. Clause 4 is the pointwise identity
on one uniform region for `|b| ≤ 1`. Neither replaces the other. For a fixed
`b` with `|b| ≤ 1`, clause 4 gives the instance of clause 3 at that `b` by the
published kernel law `germMap_eq_zero_iff` (take the same `ε`). Clause 4 says
nothing about `b` with `|b| > 1`, which clause 3 covers.

## Actual spaces, actions and quotients

Every object is the published one from `Langlands.Whittaker.JPSFunctionSpace`,
used without change. No abstract quotient, replacement action or supplied
subspace occurs.

- `Torus F n` is `H = Fin n → F.Carrierˣ` under pointwise multiplication.
  `FunctionSpace F n` is `Subrepresentation (rightTranslation ℂ (Torus F n))`:
  an actual complex space `W` of functions `H → ℂ`, stable under every
  translation `f ↦ (a ↦ f (a * s))`. Elements are `f : W.toSubmodule` with
  underlying function `f.val`. No finite-dimensionality of `W` is assumed.
- `coordinateRepresentation W i` is the source's `ρ` on the `i`-th factor
  `H_i ≅ Fˣ`. By `coordinateRepresentation_apply`,
  `(coordinateRepresentation W i b f).val a = f.val (a * coordinateEmbedding i b)`,
  that is, the `i`-th coordinate of `a` is multiplied by `b` and the others are
  unchanged.
- `coordinateVanishing W T i` is the actual subrepresentation `W_i` of all `f`
  for which one `ε > 0`, chosen before the whole tuple, gives `f.val a = 0`
  whenever `T.normalizedAbs (a i : F.Carrier) < ε`.
- `CoordinateGerm W T i` is the algebraic quotient `W / W_i`, and
  `germMap W T i` is the canonical projection. By `germMap_eq_zero_iff`, its
  kernel is exactly the uniform near-zero vanishing above.
- `sigma W T i` is the source's `σ_i`, the action of `F.Carrierˣ` on `W / W_i`
  induced by `ρ_i`. By `sigma_apply_mk`,
  `sigma W T i b (germMap W T i f) = germMap W T i (coordinateRepresentation W i b f)`.
- `IsLocallyConstantSpace W T`: every `f.val` is `IsLocallyConstant` for the
  topology on `H` determined by `T.topology`.
- `HasFiniteCoordinateOperatorSpan W T i`: the complex span of the range of
  `sigma W T i` in `Module.End ℂ (CoordinateGerm W T i)` is
  finite-dimensional. Since `σ_i` is a group homomorphism, this span contains
  the identity and is closed under composition. It is the source's algebra
  `𝒜_i`.

Not assumed: coordinate upper support (`HasCoordinateUpperSupport`), the
representation-smoothness predicate `IsSmoothSpace W T`, smoothness of `σ_i`,
finite-dimensionality of `W` or of `W / W_i`, admissibility, finite generation,
an expansion, a common stabilizer, and any dilation or uniformity certificate.

## Normalized absolute value and the bounded restriction

`|x|` is `T.normalizedAbs x`, the residue-cardinality normalization of `T`. It
is `0` at `0` and `q ^ (-T.ord x)` at `x ≠ 0`, with
`q = T.residueCardinality`. It is positive on units. For a unit `b`,
`T.normalizedAbs (b : F.Carrier) ≤ 1` says that `b` is integral. Another
normalization would rescale every threshold by a positive power and leave the
statement unchanged, including the condition `|b| ≤ 1`.

The span `S₊` in clause 2 uses exactly the source's restriction `|b| ≤ 1`. It
is the span of actual operators on `W`. Since each `ρ_i(b)` preserves `W_i`,
every element of `S₊` induces an operator on `W / W_i`. In clause 4 the
restriction `|b| ≤ 1` is also kept. For such `b` and `|a_i| < ε`, the point
`a · e_i(b)` again has `i`-th coordinate of absolute value below `ε`.

## Topology and finite functions

The body installs `T.topology` on `F.Carrier`. `PadicField` carries no other
topology instance. `F.Carrierˣ` then has Mathlib's units topology, which is
used by `Continuous η`, and `ℂ` has its usual topology. `IsLocallyConstantSpace`
installs the same `T.topology` internally.

Clause 1 is JPS's definition of a finite function on the locally compact
abelian group `Fˣ` (printed p.181): a continuous function whose translates span
a finite-dimensional space. The translates are written `a ↦ η (b * a)`, the
same convention as the published `IsFiniteFunction` on `H`. Since `Fˣ` is
commutative, this is also the span of `a ↦ η (a * b)`. The published
`IsFiniteFunction` concerns functions on `H`, not on the one coordinate group
`Fˣ`, so the condition is written out here.

## Source provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212. Registered source
`jps-1979-gl3-i`, file SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed pp.181–183 are one-based PDF pp.14–16. Worker 941 read the text layer
of all three pages and the page images of all three on 2026-10-28.

- Printed p.181, paragraph (2.2): a finite function on a locally compact
  abelian group is a continuous function whose translates span a
  finite-dimensional vector space. This is clause 1.
- Printed p.181, the remarks opening the proof of Proposition (2.2): if `σ` is
  a *smooth* representation of `Fˣ` whose operators span a finite-dimensional
  algebra `𝒜`, then `σ(a) = ∑_{χ ∈ X} χ(a) A_χ` for every `a ∈ Fˣ`, with
  finitely many finite functions `χ` and `A_χ ∈ 𝒜`. Every element of `𝒜`
  satisfies a polynomial equation, so `𝒜` is spanned by the `σ(a)` with
  `|a| ≤ 1`.
- Printed p.182, proof of Lemma (2.2.1): applying these remarks to `σ_n` gives
  a finite set `Y` of finite functions on `H_n ≅ Fˣ` and, for each `η ∈ Y`, an
  operator `A_η` in the linear span of `{ρ(b) | b ∈ H_n ≅ Fˣ, |b| ≤ 1}`, with
  `ρ(b)φ ≡ ∑_{η ∈ Y} η(b) A_η φ mod 𝒱_n` for every `φ ∈ 𝒱`. These are
  clauses 1–3. The source continues: "Thus for a given `φ ∈ 𝒱` we may find `c`
  so small that `φ(a_1, …, a_{n-1}, bc) = ∑ η(b) (A_η φ)(a_1, …, a_{n-1}, c)`
  for any `b` with `|b| ≤ 1`, any `a_i`'s." This is clause 4.
- Printed p.183, Remark (2.2.5): it extends Proposition (2.2) to finitely
  generated admissible spaces of Whittaker-type functions. It does not change
  Lemma (2.2.1) and adds no hypothesis here.

No source-specific erratum was found. Neither the project literature index,
the Library notes nor `/home/taskhub/central-library` record a correction to
JPS (1979).

## Interpretive and derived choices

- *Arbitrary coordinate.* The source performs the step for the last coordinate
  `n` inside an induction on `n`. The statement is for an arbitrary
  coordinate `i : Fin n`, with only the hypotheses concerning `i`. The source's
  argument does not use the other coordinates' hypotheses at this step.
- *Uniform region.* The source fixes one small `c` that works "for any `b` with
  `|b| ≤ 1`, any `a_i`'s". Clause 4 asks for the identity at every tuple with
  `|a_i| < ε`, not at one fixed `c`. This uniform-region form is stronger than
  the fixed-`c` form: evaluating clause 4 at a tuple whose `i`-th coordinate
  is a fixed `c` with `|c| < ε` recovers it. The threshold comes before all
  other coordinates, as in the source's "any `a_i`'s".
- *Smoothness of `σ_i`.* The source applies its p.181 remarks to `σ_n`, which
  are stated for a smooth representation. Here the only hypotheses are local
  constancy of the functions and the finite operator span. Clauses 1 and 3
  write `σ_i(b)` as `∑_{η ∈ Y} η(b) Ā_η`, with continuous `η` and fixed
  operators `Ā_η` induced on `W / W_i` by the `A_η`. So a proof of this
  statement must in effect derive the regularity of `σ_i` that the source
  takes from its smoothness assumption. That is a proof obligation, not an
  assumption.
- *Quotient identity for all `b`.* The source's congruence
  `ρ(b)φ ≡ ∑ η(b) A_η φ mod 𝒱_n` comes from `σ(a) = ∑ χ(a) A_χ` for every
  `a ∈ Fˣ`. Clause 3 therefore has no restriction on `b`. The bound `|b| ≤ 1`
  concerns the spanning family of the operators `A_η` (clause 2) and the
  pointwise identity (clause 4).
- *Operators on `W`.* The source's `A_η` lie in the span of the operators
  `ρ(b)` on `𝒱`. They are therefore endomorphisms of `W`, not of `W / W_i`.
  Clause 3 compares germs, and clause 4 evaluates `A_η f` itself.
- *Uniformity in `f`.* In the source, `Y` and the `A_η` come from `σ_n` and
  are fixed before `φ`; only `c` depends on `φ`. The statement chooses `Y` and
  `A` before every `f` and lets only `ε` depend on `f`.
- *Packaging.* `Y` is a `Finset` of functions `F.Carrierˣ → ℂ`, and `A` is a
  total function on all such functions. Only its values at members of `Y`
  enter the conclusions. The summands are written `η b • A η f` in `W` and
  `η b * (A η f).val a` in `ℂ`.
- *Excluded display.* The display after clause 4 on p.182,
  `φ(a_1, …, a_n) = ∑_{η,j} η(b) φ_j(a_n) φ(a_1, …, a_{n-1}, b_j)`, uses
  `η(b)` with `b` unbound, a typographical ambiguity. It is not part of this
  statement.

## Statement versus proof

This is a statement unit. It is a separate prerequisite of the exact proof
task for `Langlands.Whittaker.JPSDecompositionStatement`
(task b1da68dc-38c9-449e-a71c-bae1f8902b22), not the decomposition itself.
Its proof is a separate obligation. That proof may not assume
`JPSDecompositionStatement`, `Langlands.WhittakerLastEntryOneAsymptoticStatement`
or the full-torus asymptotic parent. One possible route, not established
here: obtain a common compact open subgroup of norm-one units acting trivially
near coordinate zero; use the polynomial satisfied by `σ_i(π)` for a
uniformizer `π` to get one linear recurrence in `m` for the values at
`π^m r` for finitely many unit representatives `r`; then take a finite minimum
of thresholds. The imported `JPSFunctionSpace` pair and every other existing
pair are unchanged.
