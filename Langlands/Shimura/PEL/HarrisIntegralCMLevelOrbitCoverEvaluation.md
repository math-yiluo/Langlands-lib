# Direct raw levels from morphisms of Harris orbit covers

This is an internal deduction from the actual finite-etale Harris monodromy
orbit covers and their Hom universal property, together with the actual
fibre-map-to-direct-level construction. It adds no literature theorem or
geometric existence assumption.

The number fields, algebra and schemes are in universe zero. Retain the
original central simple unitary data, normalized signature charts, abelian
family, supplied dual witness and map to the dual, full-order integral action,
and named tensor/duality, Weil-transition, adelic and torsion prerequisites.
The original test scheme is quasi-separated, connected and locally noetherian;
the geometric point field is algebraically closed. Actual finite-fibre
witnesses, invertible torsion orders and finite-etale roots of unity on that
base are inputs. A nonempty old fixed-level set at a level `U` supplies the
existing finite-monodromy-orbit construction. Both actions on Weil frames are
the existing opposite right Harris action and commuting geometric monodromy.
The raw quotient at each level uses the subgroup from `hodgeLevelFunctor`.

`harrisIntegralCMFiniteOrbitCoverFiber_pretransitive` proves that the actual
fundamental group acts pretransitively on the actual geometric fibre of the
selected cover of any old raw class. Its fibre equivalence identifies it
with the monodromy orbit of that class. Any two elements of that orbit are
related by a group element. Equivariance and injectivity of the existing
fibre equivalence transfer that relation to the actual geometric lifts.
No connectedness assertion about the selected cover is assumed or proved.

`harrisIntegralCMFiniteOrbitCoverHomRawMap` sends an actual morphism from any
finite-etale test cover into a selected orbit cover to an equivariant map
from its actual geometric fibre into the full old raw quotient. On a lift
`x` it is literally the underlying raw class of the target fibre equivalence
at `x` postcomposed with the cover morphism. Equivariance follows from the
existing Hom correspondence. The `_apply` theorem states this exact formula.
The `_injective` theorem holds for every finite-etale source: equality of the
raw maps gives equality of their orbit-valued maps by subtype extensionality,
and the existing Hom equivalence then gives equality of the cover morphisms.

`harrisIntegralCMFiniteOrbitCoverHomLevel` specializes the source to the
selected cover `Y` of a class `q` at level `V`, with its distinguished lift
`x`. The target is the selected cover of a class `r` at a level `Z`, using
the same original family and the same `U`. Put

```text
Tq = Over.mk (Y.obj.hom ≫ T.hom)
fq : Tq ⟶ T = Over.homMk Y.obj.hom rfl.
```

The construction returns a fixed raw level at `Z` on the direct family over
`Tq`, carrying the integral action literally `(relativeEndRestrict B fq).comp a`.
Quasi-separatedness of `Tq.left`, finite fibres at `x.left`, invertible torsion
orders and finite-etale roots of unity on the selected cover remain explicit
inputs. Finite-etaleness of `fq.left` follows from `Y` being an actual cover.
Apply the earlier fibre-map-to-level construction to `HomRawMap`; this uses
image containment in the lift stabilizer and the inverse actual image-fixed
restriction equivalence.

The `_val` theorem proves that actual restriction evaluation of this direct
fixed level returns exactly the target fibre equivalence's underlying raw
class at the image of the distinguished source lift. It is the earlier exact
fibre-map evaluation theorem specialized to this actual map. The `_injective`
theorem proves that the resulting direct fixed level determines the cover
morphism. Source-fibre pretransitivity is supplied by the proved theorem above;
injectivity of fibre-map-to-level construction followed by injectivity of
`HomRawMap` gives the conclusion. No transitivity premise is left to the caller.

This unit proves a map and uniqueness, without asserting that every direct raw
level arises from a cover morphism into the chosen target orbit. In particular,
image containment in a lift stabilizer is not used as an image equality.
Surjectivity, comparison on the full componentwise admissible test category,
PEL determinant/Lie and polarization/Rosati conditions, normalized rational
isogeny comparison, a moduli representing scheme, output admissibility,
smoothness, projectivity and `DivisionCMRepresentabilityStatement` remain open.
