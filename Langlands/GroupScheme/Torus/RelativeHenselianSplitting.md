# Field comparison and Henselian splitting for relative tori

This internal construction supplies `RelativeTorus.henselianSplitting`.
Let `R` be a Henselian local commutative ring, and let `R → k` be a
surjective algebra map to a separably closed field. For an actual relative
torus `T` over `Spec R`, it chooses a finite index type and an actual
group-scheme isomorphism from `T` to the corresponding standard split torus.
`RelativeTorus.SplittingData` stores these data, including the finiteness
instance needed to form the standard split torus.

The hypothesis on `T` is the published predicate `RelativeTorus.IsTorus`:
it becomes a finite split torus on an étale cover of the base. No split
presentation, constant rank, reductive ambient group, or characteristic
hypothesis is supplied separately. The conclusion concerns the whole torus
over `R`, not just its residue fibre.

The supporting theorem `RelativeTorus.IsTorus.isSplitTorus_of_henselian`
chooses a point on a splitting cover above the image of `Spec k`.
Mathlib's `Scheme.exists_fac_of_etale_of_isSepClosed` lifts that point to
an actual `k`-point of the étale cover. The published
`HenselianSections.exists_section_of_smooth_of_surjective` then extends
that point to a section over `Spec R`. The splitting over that cover
descends along the section by `IsSplitTorus.of_baseChange_of_section`,
from `Torus.SplitDescent`. The chosen definition extracts a presentation
from this proved splitting.

The module also proves that the published field predicate `IsTorus` agrees
with `RelativeTorus.IsTorus` over every field. In one direction, a point of
an étale splitting cover supplies a residue-field extension; pullback
comparison transfers the splitting to this field extension, as required by
`IsTorus`. In the other direction, the published
`torusFiniteGaloisSplitting` supplies a finite Galois splitting field.
The finite separable extension is étale, using Mathlib's
`Algebra.FormallyEtale.of_isSeparable` and finite presentation over the
Noetherian base field. Its spectrum is a surjective cover, using
`TorusExistence.surjective_algebraBaseMap`. A cover with this single member
therefore witnesses `RelativeTorus.IsTorus`. The theorem
`relativeTorus_iff_isTorus` records both directions.

These are internal deductions from the named published splitting,
pullback-comparison, and Henselian-section inputs. They make no additional
claim of correspondence with a new external source assertion. They are
supporting constructions for the special-apartment task; containment of a
prescribed subtorus, generic maximality, and the fixed-pair apartment
statement are separate obligations.

Shared declarations `IsTorus.isTorus` are imported from `Langlands.GroupScheme.Torus.RelativeFieldComparison`; their mathematical hypotheses, conclusions and data are unchanged.
