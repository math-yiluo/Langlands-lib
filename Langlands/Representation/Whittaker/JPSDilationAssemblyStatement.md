# JPS decomposition assembly from uniform coordinate dilations (statement)

Author: Worker 942. This unit states an internal conditional assembly step
for JPS (1979), Lemma (2.2.1), printed p.182. It is a proposition definition
only. Nothing here proves the assembly, the decomposition, or any of the
hypotheses, and no proof is claimed.

The statement is an internal abstraction of the source proof, not a theorem
printed in JPS. It isolates one step: passing from uniform small-coordinate
dilation formulas to the global Schwartz–Bruhat expansion. Its two family
hypotheses are premises of this helper only. They are not hypotheses of
`Langlands.Whittaker.JPSDecompositionStatement`, which is unchanged and still
unconditional. Accepting or publishing this statement, or a later proof of it,
does not prove that main target.

## Declaration

`Langlands.Whittaker.JPSDilationAssemblyStatement.{uF} : Prop`, in module
`Langlands.Representation.Whittaker.JPSDilationAssemblyStatement`. The module
imports `Langlands.Representation.Whittaker.JPSFunctionSpace` and
`Langlands.HarmonicAnalysis.Basic` and opens the namespace
`Langlands.Whittaker.JPSFunctionSpace`. It does not import
`JPSDecompositionStatement` or any Whittaker asymptotic statement. Its only
universe parameter is the unrestricted field universe `uF`. The proposition is,
in this exact order:

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  letI := T.topology
  ∀ (n : ℕ) (W : FunctionSpace F n)
    (Y : Fin n → Finset (F.Carrierˣ → ℂ))
    (A : Fin n → (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule),
    IsLocallyConstantSpace W T →
    HasCoordinateUpperSupport W T →
    (∀ i : Fin n, ∀ η ∈ Y i, Continuous η ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) →
    (∀ i : Fin n, ∀ f : W.toSubmodule,
      ∃ ε : ℝ, 0 < ε ∧
        ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < ε →
          ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
            (coordinateRepresentation W i b f).val a =
              ∑ η ∈ Y i, η b * (A i η f).val a) →
    ∃ X : Finset (Torus F n → ℂ), (∀ χ ∈ X, IsFiniteFunction T χ) ∧
      ∀ f : W.toSubmodule,
        ∃ Φ : (Torus F n → ℂ) → HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
          ∀ a : Torus F n,
            f.val a = ∑ χ ∈ X, Φ χ (fun i => (a i : F.Carrier)) * χ a
```

The type `Fin n → (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule` of `A` is the
non-dependent form of `∀ i : Fin n, (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule`;
the two are the same type.

## Quantifier order

The prime `p`, the field `F`, the topological data `T` and the rank `n : ℕ`
(zero included) are universally quantified. Then come the actual space `W`,
the finite sets `Y i` and the operator families `A i`. All of them precede
every hypothesis and every function `f`. So each `Y i` is one finite set of
functions, and each `A i η` is one operator, used for all `f ∈ W`.

In the dilation hypothesis the order is
`∀ i, ∀ f, ∃ ε > 0, ∀ a, |a_i| < ε → ∀ b, |b| ≤ 1 → …`. The threshold `ε` may
depend on the coordinate `i` and on `f`. It precedes the entire torus tuple
`a`, including all coordinates other than `i`, and every admissible `b`. A
threshold chosen separately for each `b`, or for each tuple of other
coordinates, would not satisfy this hypothesis.

In the conclusion, the finite set `X` is chosen before `f`. Its members are
actual functions on the torus, so neither the set nor its functions depend on
`f`. Only the coefficient family `Φ` is chosen after `f`. The equation holds at
every point `a` of the torus. It is not a germ identity, an eventual identity
or an identity on a subregion.

## Hypotheses

The first two hypotheses are the published definitions from
`Langlands.Whittaker.JPSFunctionSpace`, used without change.

- `IsLocallyConstantSpace W T`: every underlying function `f.val` is
  `IsLocallyConstant` on the torus `Fin n → F.Carrierˣ`, in the topology
  determined by `T.topology`.
- `HasCoordinateUpperSupport W T`: for every `f` and every coordinate `i`
  there is `R > 0` with `f.val a = 0` whenever
  `R < T.normalizedAbs (a i : F.Carrier)`. `R` precedes the whole tuple `a`,
  so the bound is uniform in the other coordinates.

The two family hypotheses are the following.

1. *Finite functions of the dilation variable.* Every `η ∈ Y i` is continuous
   on `F.Carrierˣ` in its units topology, and the complex span of its
   translates `fun a => η (b * a)`, for `b : F.Carrierˣ`, is
   finite-dimensional. This is the source's notion of a finite function on
   `Fˣ`, with the same `b * a` convention as `IsFiniteFunction`. The functions
   `η` need not be characters.
2. *Uniform bounded dilation formula.* For every coordinate `i` and every
   `f`, there is `ε > 0` such that for every tuple `a` with
   `T.normalizedAbs (a i) < ε` and every unit `b` with `T.normalizedAbs b ≤ 1`,
   `(coordinateRepresentation W i b f).val a = ∑ η ∈ Y i, η b * (A i η f).val a`.
   By the published `coordinateRepresentation_apply`, the left side is
   `f.val (a * coordinateEmbedding i b)`: the value of `f` at `a` with its
   `i`-th coordinate multiplied by `b`.

Each `A i η` is an actual complex linear endomorphism of `W.toSubmodule`. So
`A i η f` is an element of `W`, and both published hypotheses and the dilation
formula apply to it. The family `A i` is total on all functions `Fˣ → ℂ`;
only its values at the members of `Y i` enter the formula.

No other hypothesis is imposed. In particular:

- the operators `A i η` need not commute with one another or with
  translations, need not lie in the span of the bounded dilations
  `coordinateRepresentation W i b` with `|b| ≤ 1`, and need not satisfy any
  identity in the coordinate-germ quotient `CoordinateGerm W T i`;
- no unrelated supplied subspace or action has to be preserved;
- neither `HasFiniteOperatorSpans W T` nor representation smoothness
  `IsSmoothSpace W T` is assumed, and nothing is said about `sigma W T i`;
- `W` need not be finite-dimensional, admissible or finitely generated, and
  no open subgroup stabilizing all of `W` is supplied.

## Conclusion, topologies and coefficients

The conclusion has exactly the shape of the conclusion of the published
`Langlands.Whittaker.JPSDecompositionStatement`. `IsFiniteFunction T χ` is the
published predicate: `χ` is continuous on the torus and the complex span of
its translates `fun a => χ (b * a)` is finite-dimensional.

The body installs `T.topology` on `F.Carrier`. `F.Carrierˣ` then carries
Mathlib's units topology, the torus the product topology, and the additive
space `Fin n → F.Carrier` the product topology. `IsLocallyConstantSpace` and
`IsFiniteFunction` install the same `T.topology` internally, and the
continuity of each `η` in hypothesis 1 uses the same units topology.

`HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier)` is the submodule of
functions on the whole additive space `Fⁿ` that are `IsLocallyConstant` and
have `HasCompactSupport`. Each coefficient `Φ χ` is therefore locally constant
and compactly supported on all of `Fⁿ`, including the coordinate hyperplanes
where some coordinate is zero. It is evaluated on the torus through the
coordinate inclusion `a ↦ (fun i => (a i : F.Carrier))`. Arbitrary torus
functions, or functions only compactly supported on the torus, would not meet
this requirement. As in the main statement, `Φ` is a total function from all
torus functions to Schwartz–Bruhat functions; only its values on `X` matter.

`T.normalizedAbs` is the residue-cardinality normalization supplied by `T`:
it is `0` at `0` and `q ^ (-T.ord x)` at `x ≠ 0`, where
`q = T.residueCardinality`. On units it is positive.

## Rank zero

At `n = 0`, the torus and `Fin 0 → F.Carrier` are one-point spaces. The
families `Y` and `A` are indexed by the empty type, so both family hypotheses
and the upper-support hypothesis are vacuous. The statement is not excluded at
this rank. For example, the singleton `X` consisting of the constant function
`1` satisfies `IsFiniteFunction`, and for each `f` the constant coefficient
with value `f.val` at the unique point is compactly supported and locally
constant. This illustration is not part of the Lean statement.

## Source provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212. Registered source
`jps-1979-gl3-i`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
SHA256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed pp.181–183 are one-based PDF pp.14–16. Worker 942 read their text and
visually checked rendered images of all three pages on 2026-10-28. No errata
note for this source exists in the project or Library notes, and the
registered collection lists no correction to this article.

- Printed p.181: a finite function is a continuous function whose translates
  span a finite-dimensional space. The remarks before Lemma (2.2.1) give, for a
  smooth representation `σ` of `Fˣ` with finite-dimensional operator algebra
  `𝒜`, finitely many finite functions `χ` and `A_χ ∈ 𝒜` with
  `σ(a) = ∑ χ(a) A_χ`, and state that `𝒜` is spanned by the `σ(a)` with
  `|a| ≤ 1`.
- Printed p.182, Lemma (2.2.1), statement: the hypotheses and conclusion of
  the published `JPSDecompositionStatement`.
- Printed p.182, proof: by induction on `n`, the remarks give a finite set `Y`
  of finite functions on `H_n ≅ Fˣ` and operators `A_η` in the span of the
  `ρ(b)`, `|b| ≤ 1`, with `ρ(b)φ ≡ ∑_{η ∈ Y} η(b) A_η φ mod 𝒱_n`. Then, for a
  given `φ`, `c` is chosen so small that
  `φ(a_1, …, a_{n-1}, bc) = ∑ η(b) (A_η φ)(a_1, …, a_{n-1}, c)` for any `b`
  with `|b| ≤ 1` and any `a_i`'s. The next display,
  `φ(a_1, …, a_n) = ∑_{η,j} η(b) φ_j(a_n) φ(a_1, …, a_{n-1}, b_j)`, contains a
  factor `η(b)` whose variable is not explained. The proof ends with an
  induction applied to the slices `a ↦ φ(a, b)` at fixed last coordinate.
- Printed p.183: the application to Proposition (2.2) and Remark (2.2.5).
  Neither changes Lemma (2.2.1) or adds anything here.

## Derived content and its rationale

This helper is internal derived content. It abstracts the step of the proof
from the dilation formula to the final expansion, in every coordinate at once
rather than by induction on `n`.

- Hypothesis 2 is a uniform-region form of the source display with `c`. The
  source chooses one small `c` for the last coordinate. Here the formula holds
  for every tuple whose `i`-th coordinate is below `ε`, so in particular at
  every small `c` and for all other coordinates, in every coordinate `i`.
- The source's further properties of the operators (membership in the span of
  bounded dilations, the quotient congruence modulo `𝒱_n`) are deliberately
  omitted. The assembly is intended to use only hypotheses 1 and 2.
- The separate statement task 62c2957e-ecec-416d-ae03-cd4bc01cef89, the
  uniform small-coordinate dilation step from local constancy and finite
  coordinate operator span, is intended to supply both family hypotheses for
  each coordinate. Its eventual theorem, together with this helper, would then
  give the main decomposition without new hypotheses. This is a plan. Neither
  that statement nor its proof is asserted or imported here.

### Proposed proof route (unproved)

The following route, proposed in the task description by Worker 625, is
recorded only to explain why the hypotheses were chosen. It is not
established mathematics, Lean evidence or part of the statement. Every
topological and linear-algebra step in it requires proof.

- Enlarge each `Y i` to a fixed basis of the sum of the translation spans of
  its members. This absorbs the translates `η(a_i / c_i)` into one finite
  family that does not depend on the small units `c_i` chosen for `f`.
- For a given `f`, take the finitely many vectors obtained from `f` by ordered
  products of the operators `A i η`, with each coordinate used at most once.
  Choose units `c_i` with `|c_i|` below the thresholds of hypothesis 2 for all
  of these vectors, and set `r_i = |c_i| > 0`.
- Partition the torus by the set `J` of coordinates with `|a_i| ≤ r_i`. For
  `i ∈ J`, apply hypothesis 2 at the point whose `i`-th coordinate is `c_i`,
  with `b = a_i / c_i`, expanding the coordinates of `J` in a fixed order. No
  commutation of operators is needed, since hypothesis 2 applies to every
  intermediate vector and is uniform in all other coordinates.
- The resulting slices have the coordinates in `J` fixed at `c_i`. Each other
  coordinate lies in an annulus bounded below by `r_i`, and upper support of
  the intermediate vectors bounds it above. On this compact product of
  annuli the slices are locally constant. Extending them by zero and
  multiplying by the small-ball indicators in the coordinates of `J` should
  give Schwartz–Bruhat coefficients on all of `Fⁿ`.
- Products of the translated one-coordinate finite functions are re-expanded
  in one uniform finite set `X`, and coefficients of coinciding functions are
  added. The case `n = 0` is treated directly.

This route does not use the source's unexplained `η(b)` factor, and it does
not assume that local constancy in one coordinate is uniform in the other
coordinates on a compact annulus. A proof by induction through slice spaces
would instead have to prove that uniformity and the comparison of coordinate
quotients separately.

## Statement versus proof

This is a statement unit. Its proof is a separate obligation, which must not
assume or use `JPSDecompositionStatement` or either Whittaker asymptotic
parent, `Langlands.WhittakerLastEntryOneAsymptoticStatement` or the
full-torus `Langlands.WhittakerTypeAsymptoticStatement`. The imported pairs
`JPSFunctionSpace` and `HarmonicAnalysis.Basic` are unchanged, as are
`JPSDecompositionStatement` and the parent asymptotic statements.
