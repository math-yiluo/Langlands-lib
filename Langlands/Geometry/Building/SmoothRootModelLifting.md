# Zero root values from supplied smooth integral root models

This derived helper constructs an actual generic root-group point of value
zero from a supplied smooth integral root model with a nontrivial special-fibre
quotient root. The provenance is the combination of the Library's Henselian
reduction, split-unipotent torsor sections, and rational nontriviality of actual
relative root groups. It is a conditional construction for use in the
unramified root-jump descent task, not a model-existence or descent theorem.

Let `R` be any Henselian local domain with fraction field `K`. Let `j : U → G`
represent the actual relative root subgroup `RelativeRoot.subgroup i a` of a
torus homomorphism `i : S → G`. Let `M` be a supplied smooth integral model
of `U`, `φ` a supplied root function family, and `q : M.specialFibre → Q`
a supplied special-fibre group homomorphism.

`RootModelReductionCompatible` asserts two properties. Every integral section
has a generic image with nonnegative value under `φ a`. If this value is
strictly positive, its reduction has trivial image under `q`. The predicate
retains these as explicit assumptions; it does not establish either property
for any parahoric model. No root-datum-valuation axioms are required of `φ`.

`exists_zero_rootPoint_of_nontrivial_reduction` assumes a rational point `y`
of `M.specialFibre` whose image under `q` is not the identity. Smooth Henselian
reduction lifts `y` to an integral section `x`. The representing equality for
`j` puts the generic image of `x` in the actual generic root group. Its value
is nonnegative. A strictly positive value would make `q(y)` the identity, so
its value is also at most zero, including exclusion of infinity. Thus its
value is exactly zero.

`exists_zero_rootPoint_of_quotient_root` produces the required residue point
from structural quotient assumptions. It assumes that `Q` is affine and
represents, by `l : Q → L`, the actual root subgroup for a relative root `b`
of a split-torus homomorphism `iT : T → L` in a smooth affine residue group
`L`. The published `RelativeRoot.exists_rootPoint_actual` supplies a
nonidentity point in this root subgroup of `L` over the same residue field.
The representing equality gives its preimage in `Q`; that preimage is
nonidentity because homomorphisms preserve the identity. It also assumes that `q`
is the represented fppf quotient by a supplied smooth closed split-unipotent
subgroup of `M.specialFibre`. `IntegralModel.quotientReductionLift` from the
companion module first lifts this quotient point to an integral section.
Its reduction therefore has nonidentity quotient image, so the preceding
lemma applies. Rational-point surjectivity of a root chart or of an arbitrary
schematic image is not an assumption.

`smoothRootModelZeroPoint` chooses the resulting generic point.
`smoothRootModelZeroPoint_spec` verifies actual root-group membership and
value zero. The arguments retain arbitrary universes and both characteristics,
without requiring a local-field topology or a lower apartment.

These constructions leave the substantive geometric input explicit: existence
of suitable smooth integral root models and special-fibre quotients, the
nonnegative-value and positive-kernel properties, and comparison of residue
roots with affine roots and their restricted directions. None of those inputs
is derived here from a vanishing upper affine root.
