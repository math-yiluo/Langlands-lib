# Unpointed normalized CM class values from geometric families

Author: Worker 57.

This derived construction defines values of the normalized CM polarized Harris
class problem without selecting a geometric point. A value is a family over all
actual geometric points of the base, compatible with the already constructed
canonical point comparisons. Evaluation at every geometric point is proved to
be an equivalence of the entire original Harris level towers. The namespace is
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Actual points and existence

`HarrisGeometricPoint S` packages a universe-zero field `Ω`, its field and
algebraic-closedness instances, and an actual scheme morphism
`Spec Ω ⟶ S`. The record itself is in `Type 1`, so different points may have
different universe-zero algebraically closed fields. No single universal field,
embedding between point fields, or arbitrary fibre-functor comparison is an
input to this record.

`HarrisGeometricPoint.ofResidue S x` constructs such a point for every actual
topological point `x : S`. Its field is
`AlgebraicClosure (S.residueField x)` and its morphism is the composite of the
spectrum map of the residue-field inclusion with `S.fromSpecResidueField x`.
The instance `harrisGeometricPointNonempty` consequently proves existence for
every nonempty scheme, choosing only a topological point. In particular this
applies to a connected scheme, since `ConnectedSpace` includes nonemptiness.
It does not assert that the polarized moduli value is nonempty.

`HarrisGeometricPoint.comp` pushes an actual point along an actual scheme
morphism, keeping its field and algebraic-closedness instance. Its identity
and composition equations are proved by the corresponding scheme category
laws. `HarrisGeometricPoint.finiteFibers` uses the published
`geometricFiberFinite` theorem to prove finiteness of the actual lift set into
every finite-etale cover. Thus geometric-fibre finiteness is no longer an extra
point-record premise.

## Existing normalized class towers and hypotheses

The arithmetic inputs are the existing totally real number field `E`, its
quadratic CM extension `F`, central simple unitary datum `D` with algebra `A`,
imaginary quadratic CM number field `L` mapping into `F`, complex embedding
`τ₀`, and charts `C` on precisely
`harrisCMSection E (algebraMap L F) τ₀`. All these types and all schemes have
universe zero. The actual structure map `p : S ⟶ Spec F` induces the existing
normalized reflex structure `D.harrisTaylorReflexStructure C p`; the conjugated
Harris–Taylor normalization and positive auxiliary left involution are
inherited unchanged.

`geometricClassTower a` is exactly the existing
`HarrisNumericalWeilLevel.isoClassTower` at the actual point `a.hom`, using the
proved `a.finiteFibers`. Its index is the original `HarrisLevel D`, including
every compact-open transporter, subgroup transition and Hecke leg. Its values
are in `Type 1`. This retains the determinant subtype and the outer numerical
class image: one representative must satisfy both conditions. The normalized
CM comparison identifies the latter with the existence of a determinant-
compatible representative of geometric relative dimension `[E : ℚ] * n²`.
There is no additional claim that dimension is invariant under every rational
isomorphism or isogeny.

The base is quasi-separated. The tensor comparison, composition, unit,
associativity, unitor and symmetry propositions; Picard-zero pullback,
Mumford membership and universal base-change propositions; finite Weil
transition compatibility; rational profinite-integer/finite-adele comparison;
torsion finite-etaleness; invertibility of all positive full-tower orders;
finite-etaleness of the corresponding roots of unity; and positive ordered-
pair dual additivity remain explicit inputs. This module does not prove those
premises. It needs no Lie base-change naturality for its fixed-base result.

`geometricClassComparison a b` wraps the already constructed
`classGeometricPointTowerIso`. Here the base is connected and locally
Noetherian. The actual algebraically closed fields of `a` and `b` may differ.
The comparison is obtained from proved geometric-path existence and path
independence on monodromy-fixed level orbits. Its identity and composition
laws are inherited and proved as equations of natural isomorphisms; neither
these equations nor any desired equivalence is supplied as an input.

## Compatible values and their tower

For an original Harris level `U`, `CompatibleGeometricFamily U` is the subtype
of dependent functions assigning to every actual geometric point `a` a class
in `(geometricClassTower a).obj U`, subject to the equation that the canonical
comparison from `a` to `b` sends the assigned class at `a` to the assigned class
at `b`, for every pair of points. This defines a type in `Type 1`. The values
are actual existing polarized rational-isomorphism classes with their joint
normalized conditions, rather than a freely supplied output type.

`compatibleGeometricFamilyTower` acts componentwise by the existing tower's
map for every original Harris transporter. The comparison's naturality proves
that the resulting family is compatible. Function and subtype
extensionality reduce identity and composition to the corresponding existing
pointed tower laws. No level arrow or Hecke leg is omitted.

`geometricFamilyExtension a U x` extends an actual class at `a` to the family
whose component at `b` is its canonical transport from `a` to `b`. Comparison
composition proves compatibility. `geometricFamilyEvaluationEquiv a U`
evaluates a family at `a` and uses this extension as its inverse. One inverse
law is exactly the family's compatibility condition; the other is the
comparison identity law.

`geometricFamilyEvaluationIso a` assembles these equivalences into a natural
isomorphism from the compatible-family tower to the entire existing class
tower at `a`. Naturality in every original transporter is definitional, since
the family tower acts componentwise. The forward component evaluates the
family and the inverse component is the displayed extension, with both
formulas proved. `geometricFamilyEvaluationIso_comparison` proves that
evaluation at `a` followed by canonical point comparison is evaluation at
`b`. Thus these recoveries agree for independently chosen point fields.

## Provenance and remaining construction

This is a derived internal presentation of the fixed-base point-independent
class value. It is not a transcription of a new literature definition. Its
inputs and original-source context are inherited from
`HarrisTaylorCMPolarizedPointTransport`: Harris–Taylor, *The Geometry and
Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed pp.89–91,
uses connected locally Noetherian bases and invariant level orbits to obtain
canonical geometric-point comparison. The construction here uses the already
implemented comparison and coherence to form compatible families and prove
explicit evaluation equivalences. Residue fields, algebraic closure and their
spectrum maps are Mathlib constructions; actual fibre finiteness is reused
from the project's `GeometricFiberFiniteProof`.

This pair constructs fixed-base unpointed values and their original level
tower. It does not yet construct their pullback under a morphism of bases,
a presheaf in bases, the extension to disconnected bases, or equivalence with
every convention in the full original moduli problem. Representability,
scheme levels, canonical-model comparisons, coefficient descent and completion
of the host task remain separate obligations. No scheme or representability
theorem is selected or supplied by this construction.
