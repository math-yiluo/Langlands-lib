# Uniform coordinate-unit invariance for actual JPS coordinate germs

Author: Worker 454, with the mathematical interface supplied by Worker 625.
This unit defines the closed proposition
`Langlands.Whittaker.JPSCoordinateUnitInvarianceStatement.{uF}` in
`Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceStatement`.
It is an internal derived prerequisite for the regularity and uniformity
steps in JPS (1979), Lemma (2.2.1). It supplies a statement only; its
conclusion is not proved here.

## Exact parameters and hypotheses

The proposition quantifies every prime `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, and every supplied `T : F.TopologicalData`, then
installs `T.topology`. The field universe `uF` is unrestricted. It next
quantifies every `n : ℕ`, actual
`W : JPSFunctionSpace.FunctionSpace F n`, and `i : Fin n`.
The only hypotheses are

```lean
JPSFunctionSpace.IsLocallyConstantSpace W T
JPSFunctionSpace.HasFiniteCoordinateOperatorSpan W T i
```

The first means each underlying scalar function in `W` is locally constant
in the supplied product topology. The second means the complex linear span
of the operators `sigma W T i b` on the actual coordinate quotient is
finite-dimensional. Neither the function space nor its quotient is assumed
finite-dimensional. Representation smoothness, admissibility, finite
generation, upper support, and an expansion or uniformity certificate are
not hypotheses.

At `n = 0` the quantification over `i : Fin 0` is vacuous; no positive-rank
restriction is imposed.

## Actual functions, quotient, and action

All objects are imported unchanged from
`Langlands.Representation.Whittaker.JPSFunctionSpace`.
`Torus F n` is `Fin n → F.Carrierˣ`. `FunctionSpace F n` is the actual
translation-stable complex subspace represented by
`Subrepresentation (Langlands.Whittaker.rightTranslation ℂ (Torus F n))`.
For `f : W.toSubmodule`, the coordinate action evaluates as

```lean
(coordinateRepresentation W i u f).val a =
  f.val (a * coordinateEmbedding i u)
```

Thus it multiplies coordinate `a i` by `u` and leaves all other coordinates
unchanged.

`coordinateVanishing W T i` consists exactly of representatives with one
positive threshold below which they vanish for every entire torus tuple.
`CoordinateGerm W T i` is the genuine algebraic quotient of `W.toSubmodule`
by this subrepresentation's submodule. Its canonical map `germMap W T i`
is surjective, and the published kernel law `germMap_eq_zero_iff` identifies
a zero germ with this uniform vanishing property.
The action `sigma W T i` is the induced coordinate action on this quotient;
`sigma_apply_mk` states that acting on `germMap W T i f` gives the germ of
`coordinateRepresentation W i u f`. No replacement representation or
abstract supplied quotient is used.

## Subgroup, topology, and uniformity

The conclusion chooses one `U : Subgroup F.Carrierˣ` before all functions in
`W`. It requires `U` to be open and compact in Mathlib's units topology
induced by `T.topology`, and requires
`T.normalizedAbs (u : F.Carrier) = 1` for every `u ∈ U`.
The normalized absolute value is the residue-cardinality normalization of
`T`: it is zero at zero and `q ^ (-T.ord x)` for nonzero `x`, where
`q = T.residueCardinality`. Torus coordinates and units are nonzero.

The same subgroup acts trivially on the whole actual quotient:

```lean
∀ u ∈ U, ∀ q : CoordinateGerm W T i, sigma W T i u q = q
```

It also satisfies the stronger representative conclusion, in this order:

```lean
∀ f : W.toSubmodule,
  ∃ ε : ℝ, 0 < ε ∧
    ∀ a : Torus F n,
      T.normalizedAbs (a i : F.Carrier) < ε →
      ∀ u ∈ U, (coordinateRepresentation W i u f).val a = f.val a
```

The threshold may depend on `f`, with the earlier parameters fixed.
It precedes the entire tuple `a` and every unit `u ∈ U`. It is therefore
uniform in all the other coordinates and in all members of the subgroup.
The subgroup itself is independent of `f`. Separate thresholds depending
on the unit or on the other coordinates would not establish this proposition.

The quotient clause is deliberately explicit. Mathematically it follows
from the representative clause: for a fixed `u ∈ U`, the difference
`coordinateRepresentation W i u f - f` has zero germ by the kernel law.
The representative formula and surjectivity of `germMap` then give trivial
action on every germ. That implication is an explanation of the clauses,
not an additional Lean theorem in this statement unit.

## Source and internal provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), no. 1, 169–212.
Registered source `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
Printed pp.181–183 correspond to one-based PDF pp.14–16. The text of these
pages and the images of printed pp.181–182 were read.

On p.181 the finite-operator discussion starts with a smooth representation
of `Fˣ`, assumes its operator algebra is finite-dimensional, and obtains a
finite expansion by finite functions. On p.182 Lemma (2.2.1) defines the
actual coordinate quotients of a translation-invariant function space and
applies that discussion to their actions. Its proof also requires a single
small-coordinate choice uniform in the other coordinates and in every
dilation `b` with `|b| ≤ 1`.

The present assertion is not a separately stated theorem of JPS. It
isolates an internal bridge needed when the scalar-function regularity
hypothesis is formalized as `IsLocallyConstantSpace`. A common open subgroup
fixing the whole quotient supplies, in particular, the smoothness required
for the p.181 argument. The uniform representative clause supplies control
of unit dilations near zero beyond the pointwise-in-unit vanishing obtained
from quotient equality alone. The later finite-algebra expansion and
uniformity for all `|b| ≤ 1`, including nonunits of the valuation ring,
remain separate obligations.

No matching source-specific erratum was found in the supplied project,
Library, or literature notes checked. The source-specific `notes/errata`
locations were absent. This is a bounded check of available material.

## Statement status and proof obligations

The Lean file contains one `def` returning `Prop`, with no proof of this
target. In particular, local constancy is not treated as an already proved
uniform smoothness certificate. The separate exact proof must derive both
quotient regularity and the common representative thresholds from precisely
the two hypotheses above. A possible finite-operator/Baire-category route
is not a premise or established result of this unit.

The module imports only `JPSFunctionSpace`. It changes neither that pair
nor `JPSDecompositionStatement` or either Whittaker asymptotic parent, and
does not assume or prove any of those decomposition conclusions.
