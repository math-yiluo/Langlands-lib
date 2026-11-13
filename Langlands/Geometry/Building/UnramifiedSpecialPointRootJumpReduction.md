# Special-point descent from root-jump descent

`UnramifiedSpecialPointRootJumpReductionStatement` is the internal implication
from `UnramifiedRootJumpDescentStatement` to the exact published
`UnramifiedSpecialPointDescentStatement`, at every universe level. The theorem
`unramifiedSpecialPointRootJumpReduction` proves this implication. All field,
group, torus, valuation, apartment and point hypotheses of the conclusion are
retained, with no restriction on characteristic.

This is a conditional reduction. It proves neither the root-jump premise nor
the unconditional special-point descent statement. In particular, it does not
complete the proof of KP Proposition 9.9.2. Its provenance is internal: it
specializes the generic geometric theorem `isSpecialPoint_of_rootJumpDescent`
and the building/apartment comparison
`KPApartmentData.isSpecialBuildingPoint_apartmentMap_iff`. It introduces no
additional assertion from the literature.

The proof introduces the exact setting of the special-point statement and
obtains the affine, smooth and monomorphism instances from connected
reductivity and the maximal split tori. It applies the assumed root-jump
statement at the chosen Galois-fixed upper apartment point `x`. The image of
`x` being special in the building implies that `x` is special in its defining
apartment, by the building/apartment comparison. The upper torus is split,
and smoothness supplies the local finite type hypothesis of the generic
geometric theorem.

The generic theorem now reduces lower specialness to the pointwise root-jump
witnesses at `x` and the chosen lower point `w`. The special-point statement
supplies the equality between `w.val` and the restricted root-function family
at `x`. Rewriting only this value expression turns the generic witness family
into the one furnished by the root-jump premise. The last step normalizes
field, real and tensor-product instance paths and uses a definitional comparison
restricted to reducible definitions and instances. These normalization steps
change no mathematical hypothesis or conclusion.

The hypothesis identifying the whole carrier of the lower apartment is not
needed in this conditional proof: the equality at the chosen pair of points is
sufficient. The carrier hypothesis remains a binder of the exact conclusion.
The proof uses no building-descent statement or a theorem consuming such a
statement. The import of `UnramifiedBuildingDescentReduction` supplies the
published special-point target itself.
