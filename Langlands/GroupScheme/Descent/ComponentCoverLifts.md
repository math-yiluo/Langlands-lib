# Descent coherence from unique lifts on finite overlap components

Worker 416. This internal construction reduces actual group-scheme descent
coherence to isomorphisms on the supplied double-overlap components and
uniqueness on the supplied triple-overlap components. It also provides a
stronger interface requiring unique lifting of all pullback isomorphisms
on those components. All schemes have arbitrary universe `u`. Component
indices are finite types in `Type`.

`HasUniquePullbackIsoLiftsOn π T` fixes a single actual test scheme `T`.
For every pair `f g : T → S` and actual target isomorphism
`e : f*H ≅ g*H`, it requires exactly one actual group-scheme homomorphism
`a : f*C → g*C` with

```text
a ≫ g*π = f*π ≫ e.hom.
```

The construction chooses this homomorphism. Uniqueness identifies the
identity and composites with the lifts of the corresponding target
isomorphisms. The lift of the inverse is therefore its inverse, giving
`liftIso`. If this property is supplied on both `T` and `U`, the actual
pullback of the lift along `q : U → T` is the lift of the pulled-back
target isomorphism. This follows by pulling back its defining equation
and applying uniqueness on `U`. The comparisons with direct pullbacks
are the explicit `pullbackComparison`, `pullHom` and `pullIso` of
`Descent.Data`.

`HasUniquePullbackIsoLiftsOn.of_components` assumes actual component
maps `q i : Z i → T` with `Sigma.desc q` an isomorphism and the unique
lifting property on each `Z i`. For any target isomorphism over `T`, it
chooses the lifts on `Z i`. Each is conjugated by the direct/iterated
pullback comparisons, yielding a homomorphism between the actual
restrictions of the two global source pullbacks. `FiniteComponents.groupHom`
assembles these actual homomorphisms. Their defining equations imply the
global defining equation, because component restrictions detect equality.
For the same reason, component uniqueness implies global uniqueness.
Consequently unique lifting holds on `T`.

For an actual target datum `D : Datum p H`,
`Datum.liftOnOverlaps` requires unique lifting only on the actual
`Overlap p` and `Triple p`. It uses the lift of `D.overlap` as the
source overlap isomorphism. The three pullback comparisons identify its
restrictions to the triple overlap with the corresponding lifts there.
Composition preservation and `D.cocycle` prove the source cocycle.
`Datum.compatible_liftOnOverlaps` proves that `π` respects the two
data; `Datum.liftOnOverlaps_unique` proves uniqueness of the compatible
source datum.

`Datum.liftOnComponents` supplies both overlap hypotheses by
`of_components`. Its inputs are the actual finite decompositions of
the double and triple overlaps and unique lifting on each component.
It constructs an actual source datum with its overlap isomorphism and
cocycle. `Datum.compatible_liftOnComponents` proves its compatibility
with `D` along `π`.

The selected `Datum.liftFromComponentIsos` has more specific inputs.
On each double-overlap component `q i : Z i → Overlap p`, it requires an
actual isomorphism from `(q i ≫ fst p)*C` to `(q i ≫ snd p)*C` whose
forward map lifts the restriction of `D.overlap`. On each triple-overlap
component `r j : W j → Triple p`, it requires uniqueness of homomorphisms
lifting the restriction of `iso13 D.overlap`, with endpoints
`(r j ≫ p1 p)*C` and `(r j ≫ p3 p)*C`. This uniqueness is precisely the
proposition `PullbackIsoLiftUnique`; it asserts equality of any two
homomorphisms satisfying that one lifting equation. No existence on the
triple components or lifting for unrelated maps is required by this
constructor.

`FiniteComponents.pullbackIso` conjugates the given double-component
isomorphisms by the explicit pullback comparisons and assembles them
using `groupIso`. Its restriction formula identifies each direct
restriction with the original component isomorphism. The component
lifting equations therefore give the global lifting equation.
`pullHom_lift_fac` proves that any such equation persists under actual
pullback. Applied to the three triple-overlap projections, it shows that
both the composite source transport from 1 through 2 to 3 and the direct
source transport from 1 to 3 lift the target's transport from 1 to 3;
the target cocycle is used for the composite. Pull these two equations
back to each triple component. The supplied uniqueness identifies the
two homomorphisms there, and component full faithfulness gives their
global equality. This proves `cocycle_of_component_lift_unique`.
Consequently `Datum.liftFromComponentIsos` constructs an actual datum,
and `Datum.compatible_liftFromComponentIsos` proves compatibility along
`π`.

This specific-endpoint interface is useful for finite Galois descent:
its fieldwise consumer only needs to compare the covers at the actual
coordinate maps furnished by the decomposition. The stronger
`HasUniquePullbackIsoLiftsOn` interface also quantifies over unrelated
maps from a component, and is not assumed to follow from transport along
the Galois coordinate automorphisms alone.

The intended field application uses finite Galois tensor decompositions
to supply field components. Neither those decompositions nor unique
lifting for covers on their field components are proved here. The
construction invokes no field-only universal property on a nonfield
scheme and requires no lifting property on schemes outside the supplied
components. It constructs no descended object or effective solution.
Cover existence and the arbitrary-field simple-connectedness theorem
remain separate obligations.

Provenance is internal: the finite-component full-faithfulness theorem,
the explicit pullback equations in `Descent.Data`, and existence and
uniqueness in the stated hypotheses supply every step.
