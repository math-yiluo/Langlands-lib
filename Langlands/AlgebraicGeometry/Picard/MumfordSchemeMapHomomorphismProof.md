# The homomorphism equations for the actual Mumford map

Author: Worker 944.

The theorem

```lean
Langlands.AbelianScheme.relativeMumfordSchemeMapHomomorphism :
  Langlands.AbelianScheme.RelativeMumfordSchemeMapHomomorphismStatement.{u}
```

proves the imported statement in every universe `u`. It retains the canonical
pullback-tensor preservation witness, Picard-zero pullback stability,
Mumford-family Picard-zero input, quasi-separated base scheme `S`, abelian
scheme `A/S`, rigidified line bundle `L`, ordinary inverse `M`, evaluation,
and actual universal-family existence input `hA`, exactly as quantified in
the statement.

For the constructed morphism
`f = mumfordSchemeMap preservation square A L M evaluation hA`, it proves
both equations in `Over S`: the actual unit maps to `dualOrigin`, with the
specified comparison from the chosen monoidal terminal object, and addition
followed by `f` equals the pair of projection composites followed by
`dualTensor`. These are scheme-morphism equalities and therefore remain
valid after evaluation on every test scheme, including nonreduced ones.

## Implemented proof

After introducing the statement's arguments, the proof splits its two
conjuncts. The unit equation is exactly the published
`mumfordSchemeMap_unit` from `MumfordUnit`. That lemma constructs a
rigidification-compatible trivialization of the zero-parameter Mumford
family and uses injectivity of dual classification to obtain the displayed
unit equation.

For multiplication, apply `dualPointClass_injective` on the full parameter
product `A.X ⊗ A.X`. The universal family supplied by `hA` makes this
classification map injective on morphisms from that actual test scheme.
The formula `dualTensor_points` identifies the class of the right-hand
composite with the tensor of the two classified projection composites.
Its coherence inputs are the published canonical proofs
`pullbackTensorComposition` and `pullbackTensorLeftUnitor`.

Subtype extensionality reduces the equality of Picard-zero classes to
equality of their underlying rigidified classes. Three applications of
`mumfordSchemeMap_points` identify the remaining classifying maps with
the pullbacks of the actual Mumford family along multiplication and the
two projections. The resulting goal is precisely the instance of the
published theorem `mumfordBundleParameterAdditivity` at
`preservation S A L M evaluation`. The quasi-separated instance introduced
from the target supplies its base hypothesis.

The final family identity holds in the quotient by actual
rigidification-compatible isomorphisms over the entire parameter product.
Consequently the injectivity argument proves equality of the actual
scheme morphisms; it retains the full test-scheme universal property.
Family additivity is discharged by its published theorem. The explicit
Picard-zero and universal-family inputs remain those of the original
statement.

## Provenance

This module is an internal composition of the published `MumfordUnit`,
`MumfordBundleParameterAdditivityProof`, `DualSchemeTensor`, `MumfordMap`,
and canonical pullback-tensor coherence results. It completes the
classification reduction recorded in the carried private prototype.
The additivity theorem supplies the geometric family identity through
the published relative rigidified cube theorem and its two unit-axis
comparisons.

The unchanged statement's paired Markdown records the original Lan
March 14, 2021 revision and errata, the exchange from the source's second
parameter to the Library's first parameter, and the exact hypotheses.
The proof here uses family classification and tensor identities. Its
imports establish the required family identity without an additional
dual-geometry or rigidity hypothesis.
