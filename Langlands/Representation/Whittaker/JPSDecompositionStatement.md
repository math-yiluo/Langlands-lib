# JPS function-space decomposition (statement)

Author: Worker 739. This unit states the full conclusion of JPS (1979),
Lemma (2.2.1), printed p.182, for the actual function spaces and
coordinate-germ quotients published in
`Langlands.Representation.Whittaker.JPSFunctionSpace`. It is a proposition
definition only. Nothing here proves the decomposition, and no proof of it is
claimed.

## Declaration

`Langlands.Whittaker.JPSDecompositionStatement.{uF} : Prop`, in module
`Langlands.Representation.Whittaker.JPSDecompositionStatement`. The module
imports `Langlands.Representation.Whittaker.JPSFunctionSpace` and
`Langlands.HarmonicAnalysis.Basic`, and opens the namespace
`Langlands.Whittaker.JPSFunctionSpace`. Its only universe parameter is the
unrestricted field universe `uF`. The proposition is, in this exact order:

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
  letI := T.topology
  ∀ (n : ℕ) (W : FunctionSpace F n),
    IsLocallyConstantSpace W T →
    HasCoordinateUpperSupport W T →
    HasFiniteOperatorSpans W T →
    ∃ X : Finset (Torus F n → ℂ), (∀ χ ∈ X, IsFiniteFunction T χ) ∧
      ∀ f : W.toSubmodule,
        ∃ Φ : (Torus F n → ℂ) → HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
          ∀ a : Torus F n,
            f.val a = ∑ χ ∈ X, Φ χ (fun i => (a i : F.Carrier)) * χ a
```

## Quantifiers and the uniform finite family

The prime `p`, the field `F`, the supplied topological data `T`, the rank
`n : ℕ` (zero included) and the space `W` are universally quantified. After
the three hypotheses, the finite set `X` is chosen. Only then is `f`
quantified, and only the coefficient family `Φ` is chosen after `f`. So one
set `X` of functions, including the functions themselves, serves every
`f ∈ W`. The equation is required at every point `a` of the torus. It is not a
germwise equation, an eventual equation, or an equation on a subregion.

The coefficient family `Φ` is a total function from all functions
`Torus F n → ℂ` to Schwartz–Bruhat functions. Only its values at the members
of `X` enter the sum. This is equivalent to a family indexed by `X`: such a
family extends by zero, since `SchwartzBruhat` is a submodule containing `0`.
The same packaging is used by `Langlands.WhittakerLastEntryOneAsymptoticStatement`.

## Spaces, actions and hypotheses

All three hypotheses and the finite-function predicate are the published
definitions from `Langlands.Whittaker.JPSFunctionSpace`, used without change.

- `Torus F n` is the group `H = Fin n → F.Carrierˣ` under pointwise
  multiplication.
- `FunctionSpace F n` is
  `Subrepresentation (rightTranslation ℂ (Torus F n))`. A parameter `W` is an
  actual complex subspace of functions `H → ℂ`, stable under every
  translation `f ↦ (a ↦ f (a * s))`. Its elements are `f : W.toSubmodule`,
  with underlying function `f.val`. No finite-dimensionality of `W` is
  assumed.
- `IsLocallyConstantSpace W T`: every `f.val` is `IsLocallyConstant` in the
  topology of `H` determined by `T.topology`.
- `HasCoordinateUpperSupport W T`: for every `f` and every coordinate `i`
  there is `R > 0` such that `f.val a = 0` whenever
  `R < T.normalizedAbs (a i : F.Carrier)`. The bound `R` comes before the
  whole tuple `a`, so it is uniform in the other coordinates.
- `HasFiniteOperatorSpans W T`: for every coordinate `i`, the complex linear
  span of the range of `sigma W T i` is finite-dimensional. Here
  `coordinateVanishing W T i` is the actual subrepresentation `W_i` of all
  `f` vanishing when `T.normalizedAbs (a i : F.Carrier) < ε` for some
  `ε > 0` chosen before the whole tuple. `CoordinateGerm W T i` is the
  genuine algebraic quotient `W / W_i`. The action `sigma W T i` of
  `F.Carrierˣ` on it is induced by translation in the `i`-th coordinate:
  `σ_i(b)[f] = [a ↦ f (a * coordinateEmbedding i b)]`. No supplied abstract
  quotient or replacement action occurs.
- `IsFiniteFunction T χ` is exactly `Continuous χ` together with the
  finite-dimensionality of
  `Submodule.span ℂ (Set.range fun b => fun a => χ (b * a))`. It does not ask
  `χ` to be a character, a sum of characters or a smooth function.

`T.normalizedAbs` is the residue-cardinality normalization of `T`. It is `0` at
`0` and `q ^ (-T.ord x)` at `x ≠ 0`, where `q = T.residueCardinality`. On units
it is positive.

The representation-smoothness predicate `IsSmoothSpace W T` is not a
hypothesis. The source's "smooth functions" are read as locally constant
scalar functions, as recorded for the published definitions. No finite
generation, admissibility, irreducibility, supplied expansion or uniform
dilation certificate is assumed.

## Topologies and the Schwartz–Bruhat coefficients

The body installs `T.topology` on `F.Carrier`. `F.Carrierˣ` then carries
Mathlib's units topology, and `H` the product topology. The predicates
`IsLocallyConstantSpace` and `IsFiniteFunction` install the same `T.topology`
internally.

`HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier)` is the submodule of
functions on the whole additive space `Fⁿ`, with its product topology, that
are `IsLocallyConstant` and have `HasCompactSupport`. Each coefficient
`Φ χ` is therefore locally constant and compactly supported on all of `Fⁿ`,
including the points where some coordinate is zero. It is evaluated on the
torus through the coordinate inclusion `a ↦ (fun i => (a i : F.Carrier))`.
Compact support on `H` alone, arbitrary torus functions and decomposable
tensors would not meet this requirement.

## Rank zero

At `n = 0`, `H` and `Fin 0 → F.Carrier` are one-point spaces. The upper
support and operator-span hypotheses are then vacuous, and the statement is
not excluded. For instance, the singleton `X` consisting of the constant
function `1` satisfies `IsFiniteFunction`. For each `f`, the constant
coefficient with value `f.val` at the unique point is compactly supported and
locally constant. This illustration is not part of the Lean statement.

## Source provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212. Registered source
`jps-1979-gl3-i`, file SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed pp.181–183 are one-based PDF pp.14–16. Worker 739 read them in text
and visually checked the images of printed pp.181 and 182.

- Printed p.181, before Proposition (2.2): a finite function on a locally
  compact abelian group is a continuous function whose translates span a
  finite-dimensional space. This is `IsFiniteFunction`.
- Printed p.181, the remarks opening the proof of (2.2): for a smooth
  representation `σ` of `Fˣ` whose operators span a finite-dimensional
  algebra, `σ(a) = ∑ χ(a) A_χ` for finitely many finite functions `χ`. That
  algebra is spanned by the `σ(a)` with `|a| ≤ 1`. These remarks are proof
  ingredients and do not appear in the statement.
- Printed p.182, Lemma (2.2.1): `W` is a translation-invariant space of smooth
  functions on `H = ∏_{i=1}^n H_i` with `H_i ≅ Fˣ`. Each function vanishes
  when `|a_i|` is sufficiently large, for each `i`. `W_i` is the space of
  functions vanishing for `|a_i|` small enough, and `σ_i` is the
  representation of `H_i` on `W / W_i`. If the algebra `𝒜_i` spanned by the
  `σ_i(a)` is finite-dimensional for each `i`, there is a finite set `X` of
  finite functions on `H` such that every `φ ∈ W` can be written
  `φ(a) = ∑ χ(a) φ_χ(a)` with `φ_χ ∈ S(Fⁿ)` and `χ ∈ X`.
- Printed p.183, Remark (2.2.5): it extends the conclusion of
  Proposition (2.2) to finitely generated admissible spaces of Whittaker-type
  functions. It does not change Lemma (2.2.1) and adds no hypothesis here.

No source-specific erratum for this article was found. The project literature
index and `/home/taskhub/central-library` list no correction to JPS (1979). The
only nearby correction, Jacquet (2012), concerns the 1981 article *Conducteur
des représentations du groupe linéaire*.

## Interpretive and derived choices

- *Algebra versus linear span.* Since `σ_i` is a group homomorphism, the
  linear span of its range contains the identity and is closed under
  composition. It therefore equals the algebra `𝒜_i` generated by the
  operators, and the finite-dimensionality hypotheses agree.
- *Uniform vanishing.* The source's "for `|a_i|` sufficiently large" and
  "for `|a_i|` small enough" are read with thresholds uniform in the other
  coordinates, as in the published `HasCoordinateUpperSupport` and
  `coordinateVanishing`. The source proof relies on this uniformity when it
  takes `c` small "for any `a_i`'s".
- *Absolute value.* `|·|` is `T.normalizedAbs`. A different normalization
  would rescale every threshold by a positive power and leave both hypotheses
  and the conclusion unchanged.
- *Packaging.* `X` is a `Finset` of functions on `H`. Coefficients form a
  total function into `SchwartzBruhat`, and each summand is written
  `Φ χ (a) * χ a` instead of `χ(a) φ_χ(a)`, since multiplication in `ℂ`
  commutes.

## Statement versus proof

This is a statement unit. The source's proof is an induction on `n`. It uses
the remarks on smooth representations for `σ_n`, a small-coordinate dilation
expansion uniform in the other coordinates for `|b| ≤ 1`, and a uniform
choice of the inductive finite set for the slices at fixed last coordinate.
Each of these is a proof obligation for a separate proof task. In particular,
deriving the smoothness of `σ_n` used by the source's remarks from local
constancy and the finite operator span is not asserted here. The existing
definitions, the parent asymptotic statements and their imported pairs are
unchanged.
