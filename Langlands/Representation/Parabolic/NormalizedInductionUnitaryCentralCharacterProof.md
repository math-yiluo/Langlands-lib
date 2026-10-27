# The full unitary central character of actual normalized induction: proof

Authors: Worker 379 and Worker 540. The assembly follows Worker 540's private
application draft. That draft assumed the scalar clause; this module replaces
the assumption by the published scalar-action theorem.

The theorem `Langlands.glNormalizedInductionUnitaryCentralCharacter` proves
exactly the published closed proposition
`Langlands.GLNormalizedInductionUnitaryCentralCharacterStatement.{uF,uV}` from
[NormalizedInductionUnitaryCentralCharacterStatement](NormalizedInductionUnitaryCentralCharacterStatement.md).
The field universe `uF` and the carrier universe `uV` are independent. The
proof covers every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData`, every rank `n` including zero, every ordered block
shape `B`, every complex carrier `V : Type uV`, every representation `σ` of
the actual product Levi `B.Levi F.Carrier`, and every supplied
`c : UnitaryCentralCharacter σ`. It adds no hypothesis on `σ`: no smoothness,
admissibility, irreducibility, nonzero carrier, finite length, positive form,
tensor factorization or scalar-action premise. The target pair and the pairs
it imports are unchanged.

For each `c` the proof constructs

```text
cI : UnitaryCentralCharacter (T.normalizedParabolicInduced B σ)
```

with `cI.character z = c.character (B.centerToLeviCenter F.Carrier z)` for
every `z` in the full center of `GL_n(F)`. This equation holds by `rfl`.

## Reused published results

- `PadicField.TopologicalData.hasScalarCharacter_normalizedParabolicInduced`,
  from `Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`
  (Worker 264, segment proof task `5093df28`, revision 2). Its full type is:
  for `T`, `B`, `V : Type uV`, a Levi representation `σ` and a homomorphism
  `ω : F.Carrierˣ →* ℂˣ`, the hypothesis
  `Classification.HasScalarCharacter σ (B.scalarLevi F.Carrier) ω` gives,
  under `T.topology` and `T.generalLinearTopologicalGroup n`,
  `Classification.HasScalarCharacter (T.normalizedParabolicInduced B σ) GeneralLinear.scalar ω`.
  Here `HasScalarCharacter ρ z ω` means `∀ a v, ρ (z a) v = (ω a : ℂ) • v`.
  Its proof is the actual covariance calculation. Right translation by
  `a I_n` is left translation by the parabolic element
  `B.scalarParabolic F.Carrier a`. Its Levi projection is the constant block
  scalar, where the explicit block modulus, and hence its positive square root,
  equals one. The theorem has no premise beyond the displayed hypothesis.
- `GeneralLinear.BlockShape.unitaryCentralCharacterOfLeviScalar`, from
  `Langlands.Representation.Parabolic.LeviCenterRestriction`. Given `σ`,
  `c : UnitaryCentralCharacter σ`, an ambient representation `ρ` of
  `GL_n(R)`, and the action identity
  `hact : ∀ a w, ρ (GeneralLinear.scalar a) w = (c.character (B.diagonalScalarToCenter R a) : ℂ) • w`,
  it builds a `UnitaryCentralCharacter ρ` with character
  `c.character.comp (B.centerToLeviCenter R)`. The open kernel is the
  preimage of the open kernel of `c` under the continuous full-center map.
  The norm-one property comes from `c`. The action on every central element
  `z = a I_n` comes from `hact`, using Mathlib's description of the center as
  the scalar matrices. Its character equation
  `unitaryCentralCharacterOfLeviScalar_character` holds by `rfl`.

## Implemented proof

1. **Instances.** After introducing `p`, `F` and `T`, the proof installs
   `T.topology`, `T.valuativeRel` and `T.localField`. It installs
   `T.generalLinearTopologicalGroup n` after introducing `n` and `B`, as the
   statement does. The full-center constructor requires
   `IsTopologicalRing F.Carrier`. This instance comes from the local-field
   structure with the supplied valuative relation. A test without the
   valuative relation and local-field instances failed with exactly this
   missing instance. The matrix group topology is
   `T.generalLinearTopology n`, Mathlib's topology on matrix units induced by
   `T.topology`. It is therefore the topology used by the constructor and by
   the statement.
2. **The common-scalar character.** Let
   `ω = c.character.comp (B.diagonalScalarToCenter F.Carrier)`, the
   restriction of the supplied Levi character to the common scalars
   `(a I_(n_i))_i`. The underlying Levi element of
   `B.diagonalScalarToCenter F.Carrier a` is `fun i => GeneralLinear.scalar a`
   (`diagonalScalarToCenter_val`, by `rfl`). This is also
   `B.scalarLevi F.Carrier a` (`scalarLevi_apply`, by `rfl`). Hence the
   supplied field `c.acts (B.diagonalScalarToCenter F.Carrier a) v` proves
   the hypothesis
   `Classification.HasScalarCharacter σ (B.scalarLevi F.Carrier) ω` at `a`
   and `v` by definitional unfolding, with no rewriting.
3. **The scalar action on the induction.** Applying
   `T.hasScalarCharacter_normalizedParabolicInduced B` to this hypothesis gives
   `(T.normalizedParabolicInduced B σ) (a I_n) f = ω(a) • f` for every unit
   `a` and every `f` in the actual induced space. Since
   `ω(a) = c.character (B.diagonalScalarToCenter F.Carrier a)` by definition of
   the composition, this is exactly the premise `hact` of the constructor
   with `ρ = T.normalizedParabolicInduced B σ`.
4. **The full character.** The witness is
   `B.unitaryCentralCharacterOfLeviScalar F.Carrier σ c (T.normalizedParabolicInduced B σ) hact`.
   Its character is `c.character.comp (B.centerToLeviCenter F.Carrier)`, so the
   displayed formula holds by `rfl` for every full central `z`.

The representation is the published actual normalized induction from the
standard upper block parabolic, with the positive half modulus and right
translation. The proof does not alter it, and it repeats no covariance or
modulus calculation. The axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Dependencies and scope

The module imports the target statement module and
`Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`.
From that import the proof uses only the two results above and the
definitions in their types. The imported module also proves the separate
segment scalar formula, and its imports include classification statement
modules. Those statements are proposition definitions, not premises, and the
proof uses none of them. The proof uses no analytic
tempered-induction result, temperedness, exhaustion, classification,
square-integrability or Langlands-classification result. Neither ingredient
depends on this prerequisite. The published
`Parabolic.normalizedInductionCentralClause` would give the same action
identity; the proof uses the segment module's theorem as its task requires.

The provenance is internal. As the statement Markdown explains, this is the
p-adic induction specialization of the full-center pullback construction,
combined with the scalar-action calculation for normalized induction. This
module adds no claim from the literature. It proves no uniqueness of the
central character data. It proves no Haar comparison, coefficient estimate,
Jacquet bound or temperedness conclusion.
