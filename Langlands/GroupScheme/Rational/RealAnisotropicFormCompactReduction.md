# Reduction of the real anisotropic-form theorem to compact forms

Author: Worker 263.

`Langlands.GroupScheme.RealCompactFormInputs : Prop` is the conjunction of
the following three statements:

- `RealCompactFormExistenceStatement`: every complex semisimple group
  scheme has an actual real semisimple form with compact full real points.
- `RealCompactFormUniquenessStatement`: compact real semisimple groups
  with isomorphic complexifications are isomorphic over ℝ.
- `RealAnisotropicCompactnessStatement`: an anisotropic connected
  reductive real group has compact full real points.

The derived theorem `realAnisotropicForm_of_compactFormInputs` proves
that this conjunction implies exactly the unchanged published
`Langlands.GroupScheme.RealAnisotropicFormStatement`. All three inputs are
explicit hypotheses. This is a conditional reduction, and does not prove
those inputs or the unconditional target.

For existence, the proof extends the given real semisimple group to ℂ
using the published `isSemisimpleFieldExtension`. Compact-form existence
then supplies a real semisimple group `H` and the required complexification
isomorphism. Its real points are compact; the derived theorem
`isAnisotropic_of_hasCompactRealPoints` proves `IsAnisotropic H`, with the
affineness instance obtained from semisimplicity.

For uniqueness, the two anisotropic real groups have compact real points
by the third input. Composing the first supplied complexification
isomorphism with the inverse of the second gives a complexification
isomorphism between those groups. The second input then gives the required
group scheme isomorphism over ℝ.

Provenance: internal derived interface and formal composition of the
three named propositions and published field-extension theorem. The
proof has no extra universe parameters and adds no hypotheses to the
conclusion represented by `RealAnisotropicFormStatement`. The paired
statement module and its imports are unchanged.
