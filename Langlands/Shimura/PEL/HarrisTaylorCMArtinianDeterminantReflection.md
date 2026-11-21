# Reflection of the normalized determinant over local Artinian bases

`HarrisTaylorCMArtinianDeterminantReflectionStatement` concerns the actual
normalized Lie determinant of an abelian scheme already defined over a local
Artinian ring. Given a surjective ring map to a local Artinian ring, the
theorem reflects the determinant condition from the pulled-back scheme and
rational action. The structure morphism from the thicker spectrum to `Spec F`
for the CM test base field `F` is arbitrary.

The proof pulls back again to the target residue field. This composite ring
map is surjective with kernel the nilpotent maximal ideal of the source.
The residue field is formally smooth over `F`. A transcendence basis and
characteristic-zero separability give this for all residue fields in the
statement. Lifting the identity of the residue field gives a coefficient
field section that respects the induced `F`-algebra structures.

An open of the local Artinian spectrum is empty or full. The empty section
ring is subsingleton. On the full open, the section determinant on an actual
Lie chart is computed from the matrices of the rational algebra action. The
trace-dual averaging argument in `HarrisTaylorCMArtinianMatrixDeterminant`
fixes its determinant polynomial under reduction followed by the coefficient
field section. The prescribed coefficients enter the section ring through
`harrisTaylorReflexToCM C` from the cocharacter reflex field to `F`, followed
by the section map of the structure morphism. The `F`-linear section
therefore fixes the prescribed polynomial under the same operation. Lie action
naturality and restriction of the structure map identify the reductions of
these two polynomials with the equality on the pulled-back chart.
