# Natural forgetting from actual unpointed CM polarized towers

Author: Worker 57.

This derived construction forgets the actual polarization and invariant level
orbit from the existing unpointed normalized CM polarized presheaf. It
constructs a natural transformation to the restriction of the existing joint
CM action presheaf. Both functors take values in towers on the full original
Harris level and Hecke transporter category.

The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic
inputs are the universe-zero totally real number field `E`, its quadratic CM
extension `F`, an imaginary quadratic CM number field `L` with the displayed
algebra structure on `F`, the central simple unitary datum `D`, and the charts
`C` for precisely `harrisCMSection E (algebraMap L F) τ₀`. The positive auxiliary
involution and conjugated Harris--Taylor reflex convention are inherited
unchanged from the normalized polarized towers.

The base category is exactly the existing `AdmissibleCMBaseCategory`. Its
objects are actual schemes over `Spec F` satisfying connectedness, local
Noetherianity, quasi-separatedness, invertibility of all indexed positive
torsion orders, finite and etale roots of unity, the local Lie base-change
naturality proposition, positive ordered-pair additivity, and nonempty
constrained dual-evaluation data on every actual abelian scheme. Its arrows
are all actual over-category arrows between those objects. No geometric point
or fixed point field is part of an object. Neither flatness nor reducedness
is imposed. Connectedness includes nonemptiness.

The fixed tensor comparison, composition, unit coherence, associativity,
left-unitor comparison and symmetry premises remain explicit. The Picard-zero
pullback, Mumford bundle membership, universal Picard-zero base change, dual
base-change naturality, polarization stability, finite Weil transition,
rational profinite-integer/finite-adele comparison and torsion finite-etaleness
premises also remain explicit where used. The module does not prove these
geometric inputs universally.

`unpointedBaseForgetToCM` is the full-subcategory inclusion into actual
`Over (Spec F)`: it sends an object to `X.obj` and a morphism to `f.hom`.
Its identity and composition laws are reflexivity.

`geometricClassTowerForgetCMAction X a` is the existing
`forgetCMActionNatTrans` at the actual CM structure map `X.obj.hom` and the
actual geometric point `a.hom`. The imported geometric-point construction
proves the finite-fibre premise at every such point. Its target is the
constant tower on `D.HarrisTaylorCMActionClass C X.obj.hom`. This action class
retains one actual representative satisfying the normalized determinant and
prescribed dimension together.

`unpointedForgetCMActionAt X a` first evaluates the compatible family at `a`
using `unpointedClassTowerEvaluationIso`, then applies that existing forgetting
map. This is a natural transformation on every original Harris level arrow,
including all Hecke transporters.

`unpointedForgetCMActionAt_independent` proves equality for any two actual
geometric points `a` and `b`, whose algebraically closed fields may differ.
The existing canonical point-comparison theorem says that comparison followed
by forgetting at `b` equals forgetting at `a`. The compatible-family evaluation
comparison says that evaluation at `a` followed by that same comparison equals
evaluation at `b`. Composition of these two equations proves independence.
No point comparison, path, or independence equation is an added premise.

For its target, the module explicitly retains the existing action presheaf's
additional hypothesis

```text
allNaturality : ∀ S : Scheme.{0}, LieBaseChangeNaturalityStatement S.
```

`unpointedActionTowerPresheaf` is exactly

```text
(unpointedBaseForgetToCM).op
  ⋙ D.harrisTaylorCMActionPresheaf C allNaturality
  ⋙ Functor.const (HarrisLevel D).
```

The object theorem identifies its value with the constant tower on the actual
joint normalized action class. The map-value theorem identifies every level
component of a base arrow with `RationalAlgebraAction.pullbackClass` along the
actual underlying scheme morphism. This is a restriction of the existing
action presheaf.

`unpointedForgetCMAction X` implements the point-independent map by using an
arbitrary actual geometric point of `X.obj.left`. Such a point exists: the
imported construction uses an algebraic closure of an actual residue field,
and connectedness supplies a point of the scheme. The independence theorem
therefore removes dependence on that implementation choice.
`unpointedForgetCMAction_eq_evaluation` proves that this map agrees exactly
with evaluation and forgetting at every supplied actual geometric point.
`unpointedForgetCMAction_app` computes each level component on a family `x`
as forgetting `x.val a`, for every point `a`.

`unpointedForgetCMAction_naturality` proves, for every actual arrow
`f : Y ⟶ X`,

```text
unpointed pullback(f) ≫ forget(Y)
  = forget(X) ≫ action tower pullback(f).
```

The proof evaluates at an actual point `a` of `Y` and the pushed actual point
`a.comp f.hom.left` of `X`. The actual family pullback has precisely the aligned
pointed pullback as that component. The previously proved aligned forgetting
square applies to `Over.w f.hom` and the reflexive pushed-point triangle, using
the same constrained dual data on the actual pulled abelian schemes as the
unpointed pullback. Taking level components and underlying subtype values,
then applying `actionClassBaseChangeAlong_val`, identifies the result with
the restricted existing action presheaf map. Subtype extensionality closes the
equality. Proof irrelevance identifies the local Lie-naturality witness with
the global witness used by the existing target presheaf.

`unpointedForgetCMActionNatTrans` assembles those base components and their
proved naturality into a natural transformation from
`unpointedClassTowerPresheaf` to `unpointedActionTowerPresheaf`. Its component
formula is reflexivity. The result is natural in both the actual unpointed
base and the original Harris level.

Provenance is internal and derived. The imported unpointed presheaf provides
actual compatible-family values and actual base pullbacks. The geometric-point
comparison and evaluation equations prove independence, and the aligned actual
forgetting square proves base naturality. Original arithmetic and geometric
provenance remains in those imported paired modules; this pair makes no new
original-literature claim. Both normalized class subtype layers and the
same-representative joint condition are retained. No dimension invariance
under arbitrary rational isogenies is asserted.

This is a conditional construction on the stated connected locally Noetherian
admissible category, with the explicit all-scheme Lie premise in the target.
Extension to disconnected bases, precise representability, representing scheme
levels, canonical models and coefficient descent remain further constructions.
