# The actual unpointed normalized CM polarized tower presheaf

Author: Worker 57.

This derived construction assembles compatible geometric-point families and
their actual pullbacks into a presheaf on actual unpointed CM bases. The
category contains actual schemes over the CM field; no geometric point or
fixed point field belongs to a base object. The presheaf retains the full
original Harris level and Hecke transporter category.

The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic
inputs are the universe-zero totally real number field `E`, its quadratic CM
extension `F`, an imaginary quadratic CM number field `L` with the displayed
algebra structure on `F`, the central simple unitary datum `D`, and charts `C`
for precisely `harrisCMSection E (algebraMap L F) τ₀`. These are the same
arithmetic data as in the imported normalized polarized towers.

`AdmissibleCMBase` is a proposition on Mathlib's actual category
`Over (Spec F)`. An object `X` has actual scheme `X.left` and actual structural
map `X.hom : X.left ⟶ Spec F`. Its admissibility fields say:

- `X.left` is connected, locally Noetherian and quasi-separated.
- Every positive order in `Index (fun _ => True)` is a unit in its global
  sections.
- The actual roots-of-unity group scheme `mu X.left k.val` is finite and
  etale at every such order.
- `LieBaseChangeNaturalityStatement X.left` holds.
- The existing `PositivePairAdditivity` holds for actual polarized actions
  with the positive auxiliary involution determined by `D` and `C`.
- For every actual abelian scheme `B` over `X.left`, the constrained
  `DualEvaluationData preservation stability B` is nonempty.

The last premise supplies inputs on actual abelian schemes: the actual dual,
its geometry, inverse Poincare line bundle, evaluation isomorphism and dual
endomorphism additivity. It assumes neither an output polarized family nor
its pullback or functor laws. There is no separate finite-fibre premise:
finite fibres at each actual geometric point were proved in the imported
geometric-family module. The module exposes connectedness, local
Noetherianity, quasi-separatedness and roots-of-unity geometry as instances.

`AdmissibleCMBaseCategory` is the `ObjectProperty.FullSubcategory` defined
by that predicate. Thus every morphism is an actual scheme map over `Spec F`,
with its ordinary `Over` triangle and no further supplied maps or equations.
There is no restriction to flat morphisms or reduced schemes. Connectedness
here includes nonemptiness; the empty scheme and disconnected schemes are
outside this base category.

The fixed tensor pullback comparison, composition, unit coherence,
associativity, left-unitor comparison and symmetry propositions remain
explicit parameters. So do Picard-zero pullback, Mumford bundle membership,
universal Picard-zero base change, dual base-change naturality, polarization
stability, finite Weil transition compatibility, the rational
profinite-integer/finite-adele comparison and torsion finite etaleness. The
admissible category depends on exactly those fixed parameters used in its
predicate. These premises have not been proved here on all bases.

`unpointedClassTower X` is the existing
`compatibleGeometricFamilyTower` for `X.obj.hom`. At a level `U`, its value
is the subtype of families of actual normalized polarized classes at every
actual geometric point of `X.obj.left`, compatible with every canonical
point comparison. The algebraically closed field varies with the point.
The level maps act componentwise with the unchanged `HarrisLevel D` maps,
including all original inclusion and Hecke transporter arrows.

For an actual base arrow `f : Y ⟶ X`, `unpointedPullbackDualData f` chooses
constrained evaluation data only on the actual base change of each source
abelian scheme, using `Y.property.dualExists`. It uses no choice of a
geometric point of either base. `unpointedClassTowerPullback f` applies
`geometricFamilyTowerPullback` to the actual map `f.hom.left`, the actual
structure maps `X.obj.hom`, `Y.obj.hom`, and `Over.w f.hom`.
At every actual point `a` of the target base it evaluates the source family
at the actual pushed point `a.comp f.hom.left` and applies the existing
aligned polarized pullback. Compatibility is supplied by the already
proved canonical mixed square. The imported dual-choice independence
ensures equality for any other constrained choices on the same actual
pulled schemes.

`unpointedClassTowerPullback_id` applies the proved family identity law to
the identity `Over` triangle. `unpointedClassTowerPullback_comp` applies the
proved family composition law to two actual `Over` triangles, with
independently chosen constrained dual-data families for both arrows and
their composite. Proof irrelevance identifies the displayed triangle
witnesses. Thus all object values, pullback maps and functor laws are
constructed.

`unpointedClassTowerPresheaf` has type

```text
AdmissibleCMBaseCategory ... ᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1).
```

It sends an opposite base object to `unpointedClassTower X.unop` and an
opposite arrow to `unpointedClassTowerPullback f.unop`. Its composition
proof reverses the preceding contravariant composition equality.

`unpointedClassTowerEvaluationIso X a` is the explicit equivalence of towers
obtained by evaluation at any actual geometric point `a` of `X.obj.left`.
Its target is the existing `geometricClassTower` at that point, with the
normalized reflex structure forced by the same `X.obj.hom`.
`unpointedClassTowerPullback_evaluation` identifies the evaluation of every
unpointed base pullback with source evaluation at the pushed actual point
followed by `geometricFamilyPointPullback`. This is an exact equality of
natural transformations on the whole original level category.

Both imported class subtype layers and the joint same-representative
numerical conditions are retained. The construction keeps the positive
auxiliary involution and the conjugated Harris--Taylor reflex convention;
it makes no claim that dimension is invariant under arbitrary rational
isogenies.

Provenance is internal and derived. Mathlib's actual `Over` and full
subcategory constructions organize the compatible families and actual
pullback laws from `HarrisTaylorCMPolarizedFamilyBaseChange`, with their
existing arithmetic and geometric provenance. This pair makes no new
original-literature assertion. It constructs a conditional unpointed
polarized tower presheaf on the stated connected locally Noetherian
admissible category. Extension over disconnected bases, representability,
representing scheme levels, canonical models and coefficient descent
remain further constructions.
