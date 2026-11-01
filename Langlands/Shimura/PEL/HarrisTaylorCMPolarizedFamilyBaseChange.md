# Actual pullback of compatible normalized CM polarized families

Author: Worker 57.

This derived construction supplies actual varying-base maps on the compatible
geometric-point families defined in `HarrisTaylorCMPolarizedGeometricFamilies`.
It proves compatibility, naturality in every original Harris transporter,
identity, composition and independence from constrained dual-evaluation choices.
It uses the actual polarized base-change maps and their existing mixed
point/base-change square.

The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. All arithmetic
fields have universe zero. The fixed inputs are the totally real number field
`E`, its quadratic CM extension `F`, an imaginary quadratic CM number field
`L` with the displayed algebra structure on `F`, a central simple unitary datum
`D`, and signature charts `C` for exactly
`harrisCMSection E (algebraMap L F) τ₀`. The normalized reflex structure at
`p : S ⟶ Spec F` is the existing `D.harrisTaylorReflexStructure C p`; it is
transported together with the same CM structure map.

The actual schemes `S` and `T` are connected, locally Noetherian and
quasi-separated. An actual scheme map `b : T ⟶ S` and actual structure maps
`p : S ⟶ Spec F`, `q : T ⟶ Spec F` satisfy the displayed triangle
`hp : b ≫ p = q`. No flatness or reducedness condition is imposed on `b` or
the bases. Each base has the following explicit prerequisites:

- All positive orders in `Index (fun _ => True)` are units in global sections.
- The actual roots-of-unity group schemes at these orders are finite and etale.
- `PositivePairAdditivity` holds for the existing actual polarized actions.

The source additionally satisfies `LieBaseChangeNaturalityStatement S`.
A displayed family `dualData` gives
`PositivePullbackDualData ... b X` for every actual source
`PositivePolarizedAction X`. These are constrained evaluation data on the
actual base-changed abelian scheme, not an assumed class map or functor law.
The fixed tensor comparison, composition, unit, associativity, left-unitor and
symmetry propositions remain explicit, as do Picard-zero pullback, Mumford
bundle membership, universal Picard-zero base change, dual base-change
naturality, polarization stability, finite Weil transition compatibility,
the rational profinite-integer/finite-adele comparison and torsion finite
etaleness. All are the named parameters of the imported constructions.

For an actual geometric point `a` of `T`, `a.comp b` is the actual point of
`S` with the same algebraically closed field and homomorphism `a.hom ≫ b`.
Their finite-cover fibres are finite by the existing proved `finiteFibers`
theorem, rather than an extra assumption. `geometricFamilyPointPullback a`
applies `classTowerBaseChangeAlong` to this pair of points, `hp`, and the
reflexive point triangle. Thus its source and target are the existing actual
normalized polarized class towers at `a.comp b` and `a`, respectively.
It includes every original inclusion and Hecke transporter arrow.

`geometricFamilyPointPullback_comparison` proves that for any two actual
points `a`, `a'`, including points with distinct algebraically closed fields,

```text
comparison_S(a.comp b, a'.comp b) ≫ pullAt(a')
  = pullAt(a) ≫ comparison_T(a, a').
```

The proof eliminates the structure-map equality `hp`, then identifies both
sides with the existing canonical `classTowerGeometricBaseChange`: its
pushed-source-comparison formula gives the left side and its
target-comparison formula gives the right side. The existing normalized
mixed square is the mathematical input to those formulas. No additional
path or comparison coherence is assumed.

`geometricFamilyTowerPullback` sends a compatible family `x` over `S` to the
family whose value at every actual target point `a` is

```text
pullAt(a) (x(a.comp b)).
```

The preceding square and `x`'s source compatibility prove the output family's
compatibility. Naturality is the componentwise naturality of `pullAt(a)`.
`geometricFamilyTowerPullback_app` records the formula.
`geometricFamilyTowerPullback_evaluation` gives its exact factorization
through source evaluation at `a.comp b` and target evaluation at `a`, as
an equality of natural transformations of the full original Harris towers.

`geometricFamilyTowerPullback_dualData` proves equality of the resulting
family maps for any independent second constrained dual-data family on `b`.
It applies the existing aligned dual-choice independence at every actual
point and then uses subtype and function extensionality.

`geometricFamilyTowerPullback_id` proves that the family map along the
identity scheme morphism and its unit structure triangle is the identity
natural transformation. After subtype and function extensionality and
unpacking the actual point, the formula is the component of
`classTowerBaseChangeAlong_id`. Only the point's actual field and morphism
are unpacked; no geometric point is chosen for the base.

For actual maps `b : T ⟶ S`, `c : R ⟶ T`, actual CM structure maps `p`,
`q`, `v`, and triangles `b ≫ p = q`, `c ≫ q = v`,
`geometricFamilyTowerPullback_comp` proves

```text
pullback(b) ≫ pullback(c) = pullback(c ≫ b).
```

The third base has the same stated geometric, units, roots-of-unity and
additivity prerequisites; the intermediate base additionally supplies Lie
base-change naturality. All three arrows use independently supplied
constrained dual-data families. The composite structure triangle is the
explicit associativity/transitivity composite in the Lean statement.
The proof again uses family extensionality and unpacks an arbitrary actual
point of `R`; the resulting equality is precisely the component of
`classTowerBaseChangeAlong_comp`, with the successive actual pushed points.

The class types retain both imported subtype layers, the same original
polarized representative for the joint numerical conditions, the positive
auxiliary involution and the conjugated Harris--Taylor normalization.
These proofs never assert dimension invariance under all rational isogenies
or replace an actual inverse with a formal relation.

Provenance is internal and derived from the imported paired modules:
`HarrisTaylorCMPolarizedGeometricFamilies`,
`HarrisTaylorCMPolarizedPointBaseChange` and
`HarrisTaylorCMPolarizedAlignedBaseChange`. This pair makes no new
original-literature assertion. It constructs pullback and its laws under
the displayed prerequisites. Assembly into a category of admissible
unpointed bases, extension across disconnected bases, representability,
representing scheme levels and coefficient descent remain further work.
