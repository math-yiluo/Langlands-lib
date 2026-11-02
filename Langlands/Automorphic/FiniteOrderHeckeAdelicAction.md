# Full adelic action on actual finite-order Hecke lines

Fix `F : Type uF` with `Field F` and `NumberField F`, any `n : ℕ`, a complex
`HeckeCharacter F` denoted `χ`, and `hχ : χ.HasFiniteOrder`. Coefficients are
the usual complex field. There is no restriction on the number-field universe
or the natural matrix rank, including rank zero, and no compactness assumption
on an adelic quotient.

This internal construction uses the published actual function line
`realization F n χ hχ`, its `scalarEquiv`, and its constructed `unitaryForm`
from `FiniteOrderHeckeRealization` and `FiniteOrderHeckeUnitaryForm`. Those
inputs are definitions built from `χ` and `hχ`; this module does not take an
additional positive-form or globalization existence hypothesis.
`scalarEquiv c` represents the full adelic function

`x ↦ (χ.adelicDeterminant n x : ℂ) * c`.

`adelicRepresentation` is the scalar twist of the trivial representation on
this original function carrier by the actual continuous determinant character
of `AdelicGL F n`. In particular it is a representation of the full adelic
group, with value `(χ.adelicDeterminant n g : ℂ) • f`, rather than just an action
of its finite or compact subgroup. Its representation laws come from the
published twist construction. `adelicRepresentation_scalarEquiv` gives its
scalar-coordinate formula.

`evaluate_adelicRepresentation` proves that its value as an actual represented
function is positive right translation:

`evaluate (R(g) f) x = evaluate f (x * g)`.

The proof applies the generic `scalarEquiv_right_translation` to the published
evaluation formula. Surjectivity of the original scalar equivalence and
multiplicativity of the determinant character identify the functions.
`adelicRepresentation_ofFinite` and `adelicRepresentation_ofCompact` prove
equality with the original finite and standard infinite compact operators on
every original vector. They use the published scalar-coordinate formulas and
`operator_eq_smul_of_scalarEquiv`. There is no inverse-character convention
change.

`adelicDeterminant_norm` applies the published finite-order unitarity theorem
to the idele class of the determinant of `g`. Thus every scalar multiplier has
norm one. `adelicUnitaryForm` applies `scalarActionForm` to the chosen finite
form and this norm identity. It has exactly the chosen finite form's
`toInnerProductCore`, as also reflected by `adelicUnitaryForm_inner`.
The original compact form retains this same core as well. The three
form-dependent completions, their norms, topologies and canonical embeddings
therefore agree definitionally.

Write `b := unitaryForm F n χ hχ` and `H := b.finiteForm.HilbertCompletion`.
The main constructor `completedAdelicAction` is a continuous map

`AdelicGL F n × H → H`

whose value is the completed representation of `adelicUnitaryForm`. It is
therefore an actual action on the same Hilbert completion already used for the
finite and compact actions. Its scalar formula is

`completedAdelicAction (g, x) = (χ.adelicDeterminant n g : ℂ) • x`.

The generic density argument for scalar completed operators proves this
formula. Continuity of the determinant character followed by the continuous
value map `ℂˣ → ℂ`, and continuous scalar multiplication on `H`, prove joint
continuity for the existing full adelic topology.
`completedAdelicAction_toHilbert` proves equivariance of the unchanged canonical
embedding. The group laws, inverse operators, norm preservation and inner
product preservation are inherited from
`adelicUnitaryForm.completedRepresentation` and its `completedOperator`.

`completedAdelicAction_ofFinite` and `completedAdelicAction_ofCompact` identify
the restrictions on every completed vector with `b.finiteForm.completedOperator`
and `b.compactForm.completedOperator`, respectively. For each, the original
restriction identity and `completedOperator_eq_smul` identify the restricted
completed operator with the same scalar as the full action. These statements
use `H` directly, including for the compact operator; no transport of Hilbert
spaces or change of topology is involved.

The provenance is the explicit composition of the published determinant-line,
positive-form, twist and actual completion constructions with the generic
scalar-action lemmas in `Representation.Unitary.ScalarAction`. No new
identification with an original-literature theorem is made. This gives a full
adelic unitary action for these supplied finite-order character lines. It does
not assert general automorphic globalization, spectral occurrence, an
invariant-integral model, recovery of all smooth vectors, or a
differential-operator extension to every completed vector.
