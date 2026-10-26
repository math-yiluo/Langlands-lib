# JPS function spaces and coordinate germs

Author: Worker 625. This definition unit constructs the function spaces, invariant
subspaces, and quotient actions from JPS (1979), Lemma (2.2.1), printed p.182.
It does not state or prove that lemma's decomposition conclusion.

All declarations are in `Langlands.Whittaker.JPSFunctionSpace`. They work over
every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData`, and every `n : ℕ`. The field universe is unrestricted.

## Spaces and translations

`Torus F n` is the actual group `Fin n → F.Carrierˣ`, with pointwise
multiplication. `FunctionSpace F n` is exactly
`Subrepresentation (Langlands.Whittaker.rightTranslation ℂ (Torus F n))`.
A parameter `W` therefore consists of an actual complex linear subspace of
functions on that group, certified stable under translation. Its carrier is
`W.toSubmodule`; no smoothness or support condition is bundled into it.

`coordinateEmbedding i : F.Carrierˣ →* Torus F n` sends `b` to the tuple with
`b` in coordinate `i` and one elsewhere. The evaluation laws
`coordinateEmbedding_apply`, `coordinateEmbedding_same`, and
`mul_coordinateEmbedding` identify multiplication by this tuple with
`Function.update a i (a i * b)`. The restricted action
`coordinateRepresentation W i` is `W.toRepresentation.comp (coordinateEmbedding i)`.
`translate_apply`, `coordinateRepresentation_apply`, and
`coordinateRepresentation_apply_update` evaluate the underlying representative
as `f(a * s)` and `f(a * coordinateEmbedding i b)`, respectively.
`coordinateEmbedding_commute` and `coordinateRepresentation_commute` prove
that these coordinate operations commute, including when the indices coincide.
These are structural facts about the abelian coordinate group.

## Uniform support and the actual coordinate quotient

`HasCoordinateUpperSupport W T` means

```lean
∀ f : W.toSubmodule, ∀ i : Fin n, ∃ R : ℝ, 0 < R ∧
  ∀ a : Torus F n, R < T.normalizedAbs (a i : F.Carrier) → f.val a = 0
```

The bound may depend on `f` and `i`. It is uniform in every other coordinate:
`a` is quantified after `R`. This is a bound separately in each coordinate,
not a claim of compact support on the multiplicative torus.

`VanishesNearCoordinateZero T i f` means

```lean
∃ ε : ℝ, 0 < ε ∧
  ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < ε → f a = 0
```

Here too the threshold is chosen before the entire tuple `a`. The absolute
value is the residue-cardinality normalization supplied by `T`: it is zero at
zero and equals `q ^ (-T.ord x)` at nonzero `x`, where
`q = T.residueCardinality`. Arguments `a i` are units, so their absolute values
are positive. No spectral norm or unspecified absolute value is substituted.

The lemmas `vanishesNearCoordinateZero_zero`, `_add`, `_smul`, and `_translate`
prove closure under zero, addition, scalar multiplication, and every translation.
For a sum the proof uses the minimum of the two positive thresholds. For a
translate `f(a * s)` it uses `ε / T.normalizedAbs (s i)`; positivity and
multiplicativity of the normalized absolute value prove the bound. Thus the
threshold remains uniform in all other coordinates.

`coordinateVanishing W T i` constructs the actual subrepresentation of
`W.toRepresentation` with exactly this membership predicate. It is the source's
`W_i`. The lemma `mem_coordinateVanishing_iff` is its defining membership law.
`CoordinateGerm W T i` is the genuine algebraic quotient
`W.toSubmodule ⧸ (coordinateVanishing W T i).toSubmodule`.
`germRepresentation` uses Mathlib's `Representation.quotient`; `germMap` is its
canonical surjective projection as an intertwiner. `germMap_eq_zero_iff`
identifies its kernel precisely with uniform near-zero vanishing.

`sigma W T i : Representation ℂ F.Carrierˣ (CoordinateGerm W T i)` is the
restriction of `germRepresentation` along `coordinateEmbedding i`. It is the
actual action `σ_i` in the source, with no supplied replacement subspace or
action. `germRepresentation_apply_mk` and `sigma_apply_mk` give the formulas
on quotient representatives. Together with `coordinateRepresentation_apply`
they state `σ_i(b)[f] = [a ↦ f(a * coordinateEmbedding i b)]`.
`sigma_translate_commute` proves commutation with all full-torus translations
on this quotient. There is no evaluation of a quotient germ at a point:
evaluation is asserted only for its function representatives.

`HasFiniteCoordinateOperatorSpan W T i` is exactly

```lean
FiniteDimensional ℂ (Submodule.span ℂ (Set.range (sigma W T i)))
```

The range consists of complex linear endomorphisms of this actual quotient,
not of functions on `H` or of endomorphisms of an unrelated module.
`HasFiniteOperatorSpans W T` quantifies this hypothesis over all `i`.
These definitions impose no finite-dimensionality condition on `W` itself.

## Separate regularity hypotheses and finite functions

Each topological predicate explicitly installs `T.topology`; the topology on
units and the product topology on the torus are then inherited from it.
`IsSmoothSpace W T` is precisely `Langlands.IsSmooth W.toRepresentation` in
that topology: every vector is fixed by some open subgroup, uniformly on the
entire function domain. `IsLocallyConstantSpace W T` instead means every
underlying function `f.val` is `IsLocallyConstant`, the scalar-function
interpretation of the source's smooth functions over a nonarchimedean field.
These are recorded as distinct predicates. No implication or equivalence
between them is asserted here, and neither is needed for the algebraic
quotient construction. A later theorem using representation smoothness must
state it explicitly or prove a suitable bridge from its hypotheses.

`IsFiniteFunction T χ` is exactly

```lean
Continuous χ ∧
  FiniteDimensional ℂ (Submodule.span ℂ
    (Set.range fun b : Torus F n => fun a => χ (b * a)))
```

in the supplied topology. This reproduces the `b * a` convention of
`Langlands.WhittakerLastEntryOneAsymptoticStatement`. The algebraic right
translation above uses `a * b`; they agree on this abelian group, but no parent
statement or imported pair is changed. A finite function need not be a
character. No smoothness claim about finite functions is included.

At `n = 0` both `Torus F 0` and the additive space `Fin 0 → F.Carrier` are
singleton spaces. The function-space definition still makes sense, upper
support and all-coordinate finite-operator-span conditions are vacuous, and
there is no `i : Fin 0` for which a coordinate quotient must be formed.
All declarations retain this rank without any positivity assumption on `n`.

## Source and scope

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212. Registered source
`jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Proposition (2.2), its proof, Lemma (2.2.1), and Remark (2.2.5), printed
pp.181–183 (one-based PDF pp.14–16), were read in text and visually checked.
No matching source-specific erratum was found in the supplied project and
Library notes; the supplied `notes/errata` directories were absent.

The source defines finite functions immediately before Proposition (2.2),
and defines the actual spaces and coordinate quotients in Lemma (2.2.1).
The monoid homomorphisms, representative formulas, closure proofs, and quotient
intertwiner here are derived structural constructions implementing those
spaces with the Library's right-translation convention and Mathlib's quotient
machinery. The distinction between representation smoothness and locally
constant scalar functions is explicit additional interface bookkeeping.

This unit supplies neither the decomposition theorem nor any uniform
small-dilation expansion, Jacquet vanishing, or finite operator-span theorem.
In particular the source proof's restriction `|b| ≤ 1`, its uniform
small-coordinate threshold, and the eventual single finite set of functions
chosen before `f` remain obligations for separate statement and proof units.
