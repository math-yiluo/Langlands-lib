# Pointed-morphism rigidity over every field

`Langlands.AbelianScheme.fieldPointedMorphismRigidity.{u}` proves exactly
the published proposition
`Langlands.AbelianScheme.FieldPointedMorphismRigidity.{u}`. The universe
`u` and field `K : Type u` are arbitrary. For actual group schemes
`A H : GroupScheme (Spec K)`, assume that `A` is smooth, proper, and
geometrically connected, and that `H` is locally of finite presentation,
quasi-compact, and quasi-separated over `K`. Every morphism
`f : A.X ⟶ H.X` satisfying `η[A.X] ≫ f = η[H.X]` then satisfies
`IsMonHom f`, so preserves multiplication as well as the unit.

The statement and its imports are unchanged. No commutativity, restriction
on the field, or homomorphism structure on `f` is an additional hypothesis.
The proof imports the published smooth-integrality, field-separatedness,
and algebraically closed two-axis rigidity theorems. It does not use
arbitrary-base pointed-morphism rigidity.

## Implemented proof

The published theorem `Langlands.GroupScheme.fieldSeparated`, imported
from `Langlands.GroupScheme.FieldSeparatedProof`, states that every group
scheme over an arbitrary field has separated structure morphism, without
additional hypotheses. Its companion Markdown explains the proof through
the closed unit section and the diagonal pullback, corresponding to
[Stacks Project Tag 047L](https://stacks.math.columbia.edu/tag/047L),
registered as `stacks-group-scheme-field-separated-047l-2026-10-22`.

For a unit-preserving map, consider the morphism

```text
d : A × A ⟶ H,     d(x,y) = f(xy)/(f(x)f(y)).
```

All operations here are those on morphisms into the group object `H`.
The order of factors is fixed as written and needs no commutativity.
`defect_left_axis` and `defect_right_axis` use the unit laws and the
given unit-preservation equation to show that `d` is the unit on both
axes. `isMonHom_of_defect_eq_one` shows that `d = 1` implies multiplication
preservation: `div_eq_one` gives `f(xy) = f(x)f(y)`, and the categorical
product identities put this in the form required by `IsMonHom`.

The main proof installs the given geometric properties as local instances.
The published theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality`, imported from
`SmoothGeometricIntegralityProof`, gives geometric integrality of `A`
over the original arbitrary field. Let `b : Spec (AlgebraicClosure K) ⟶
Spec K` be the field-extension map, let `F = Over.pullback b`, and let
`A'` and `H'` be the pulled-back group objects.

Properness of `A'` follows by base change. Mathlib's geometric-integrality
instances supply integrality of `A' × A'`. Applying the published
`Langlands.GroupScheme.fieldSeparated` to `AlgebraicClosure K` and `H'`
gives separatedness of `H'`. Base change of local finite presentation
gives its local finite type property. Unit preservation also transports
along `F`.

The published theorem
`Langlands.AbelianScheme.algebraicallyClosedTwoAxisRigidity`, imported
from `AlgebraicallyClosedTwoAxisRigidityProof`, now applies to the defect
of `F.map f`. Its inputs are properness of `A'`, integrality of the
product, separatedness and local finite type of `H'`, and the two axis
identities. It says that this defect is the constant unit map. Thus
`F.map f` is a monoid-object homomorphism.

Finally, `map_defect_eq_one` uses functoriality of multiplication and
inverse to show that `F` maps the original defect to the unit whenever
`F.map f` is a homomorphism. Pullback along the field extension is
faithful, as supplied by Mathlib. Applying `F.map_injective` descends
the equation `d = 1` to `K`. The defect criterion gives `IsMonHom f`.
This proves the target over every field, including fields that are not
algebraically closed.

## Provenance and contributions

The unchanged statement's companion Markdown records its specialization
of Lan, Corollary 1.3.1.6, together with the corrected rigidity hypotheses
in the 2021 errata and revision, the GIT predecessor, and the field
separatedness result. This proof is an internal assembly following a
different route: the two-axis theorem is applied after algebraic-closure
base change, then equality of morphisms is descended faithfully.

Worker 334 implemented the axis calculations and assembly. The helpers
`isMonHom_of_defect_eq_one` and
`map_defect_eq_one` adapt Worker 143's private
`PointedRigidityAssembly`, revision 5; Worker 143 is a contributing
coauthor. These adapted helpers have complete proofs here and do not
import or assume the parent rigidity theorem.

The descent follows the pattern of Mathlib's
`isCommMonObj_of_isProper_of_geometricallyIntegral`, by Andrew Yang and
Christian Merten (Apache 2.0), with the morphism defect replacing the
commutator. The geometric results themselves are reused through their
published theorem names: the smooth-integrality proof is by Worker 416,
the field-separatedness proof is by Worker 810, and the two-axis proof is
by Worker 423 with contributions by Worker 334. Their companion Markdown
files explain their implementations and sources.
