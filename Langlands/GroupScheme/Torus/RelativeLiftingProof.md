# Pointed etale lifting of an actual closed split torus

Authors: Worker 1558, Worker 1583, and Worker 1683.

`Langlands.GroupScheme.relativeSplitTorusLifting.{u}` proves the exact
published proposition `RelativeSplitTorusLiftingStatement.{u}`. For every
scheme `S`, smooth affine group scheme `G/S`, and supplied closed split
torus inclusion in the actual residue fibre at `s`, it constructs a split
torus and closed inclusion over an etale neighbourhood with a point over
the original residue field. It recovers the supplied inclusion under the
actual base-change comparisons. The universe `u` is arbitrary. There is
no reducedness, Noetherian, characteristic, or connected-fibre hypothesis.

## Implemented construction

Write `c = S.fromSpecResidueField s`. A splitting of the supplied torus
`T₀` chooses a finite index type `I` and an actual group-scheme isomorphism
with the standard split torus. Set `H = splitTorus S I`. The standard
base-change isomorphism and the chosen splitting give an actual
isomorphism `e₀ : H_c ≅ T₀`. Composing its forward map with the supplied
closed inclusion `i₀` gives a closed homomorphism `j₀ : H_c ⟶ G_c`.

The published theorem `HomScheme.smoothSplitSourceRepresentability`
supplies a smooth parameter scheme `M/S` with an actual universal
homomorphism `i : H_M ⟶ G_M`. Its universality on every test scheme gives
a parameter `x : Spec κ(s) → M` whose evaluation is exactly `j₀`.
This representability theorem is proved in the imported Library module;
it is not an additional premise of the lifting theorem.

`HomScheme.isClosedImmersion_evaluate_iff` translates that equality to
closed immersion of the raw pullback of `i` along `x`.
`exists_open_isClosedImmersion_baseChange` then supplies an open
immersion `q : V → M`, a lift `bx : Spec κ(s) → V` satisfying
`bx ≫ q = x`, and closed immersion of the universal homomorphism on `V`.
The affine hypothesis for its target follows by base change from
`G → S`. The composite `V → M → S` is smooth and takes `bx` to `c`.

Apply `Langlands.AlgebraicGeometry.exists_pointed_etale_section` to this
smooth composite and the specified point `bx`. It gives `p : U → S`,
`b : Spec κ(s) → U`, and `a : U → V` such that `p` is etale,
`b ≫ p = c`, `a ≫ (q ≫ M.hom) = p`, and `b ≫ a = bx`.
In particular the residue-field-valued point is retained exactly.

Define the lifted torus to be `T = H_U`, which is split by base change
of the chosen standard split torus. Define its actual homomorphism
`j : T ⟶ G_U` by evaluating `i` at the composite parameter `U → V → M`.
Evaluation is compatible with composition. Thus `j` is a closed immersion
because it is the pullback, through the actual comparison isomorphisms,
of the closed family on `V`.

The equalities for `b`, `a`, `bx`, and `q` identify the composite parameter
`Spec κ(s) → U → M` with `x`. Composition of evaluation therefore gives
exactly `evaluate b j = e₀.hom ≫ i₀`, expressed in the relevant over
categories. Finally `HomScheme.recover_fibre_inclusion` constructs the
actual isomorphism `e : T_b ≅ T₀`. Its underlying comparison is
`HomScheme.fibreComparisonIso`, the iterated-pullback comparison followed
by `e₀`. The resulting equality is precisely

```text
(baseChange b).map j ≫ (baseChangeCompIso p b G).inv ≫
  (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom =
    e.hom ≫ i₀.
```

This is the equality required by the unchanged target statement.

## Pointed splitting and provenance

The lifted source is chosen as a standard split torus over `S` before
constructing the parameter space. Consequently its pullback to `U` is
already split. The supplied special-fibre splitting enters `e₀`, and
universality chooses the parameter of that exact inclusion. The pointed
smooth-section construction preserves that parameter and the original
residue field. This implements the pointed splitting refinement directly.

This module is an internal assembly of the published Hom representability,
closed-immersion neighbourhood, pointed smooth-section, and fibre-comparison
proofs. Their companions describe the underlying constructions. It supplies
the split-torus lifting proposition isolated by the target statement without
using that proposition, a supplied local model, or an unconstructed subgroup
as a premise. Worker 1558 authored the Hom interface, fibre comparison and
assembly; Worker 1583 authored the closed-immersion neighbourhood development;
Worker 1683 authored the pointed smooth-section construction.
