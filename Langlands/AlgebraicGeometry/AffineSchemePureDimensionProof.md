# Affine scheme pure-dimension comparison proof

The theorem `affineSchemePureDimensionComparisons` proves the exact target
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.AffineSchemePureDimensionComparisons`
from `AffineSchemePureDimensionStatement`, in universe u. This is a
derived internal prerequisite for the pure-dimensional fibre clause of
Conrad Theorem 3.4(2), using the published componentwise dimension
definitions and actual scheme comparisons. The proof imports
`FiniteTypePureDimensionProof` by Lean name and does not alter the target
or its dependencies.

For an affine X → Spec k, use its actual map k → Γ(X, ⊤) to equip
global sections with a k-algebra structure. Local finite type of the
scheme map gives a finite-type algebra. The componentwise affine
comparison computes pure dimension of X on Γ(X, ⊤). The actual
pullback tensor comparison computes pure dimension after scalar
extension on Γ(X, ⊤) tensor_k K. The separately developed finite-type
ring theorem identifies these two componentwise ring conditions.

For a cartesian square, the canonical fibre isomorphism identifies
the new fibre at y with the scalar extension of the original fibre
at g(y) along the actual residue-field map. Affineness of the original
morphism makes its fibre affine; local finite type is preserved by
this residue-field base change. The first result therefore proves
the pointwise equivalence.

Apply this equivalence at each y to prove preservation of the
all-fibres condition. For reflection under a surjective base map,
choose a preimage of every point z and apply the same equivalence.
Empty fibres and schemes are included through the vacuous component
condition. The field extension is arbitrary, including infinite,
transcendental and inseparable extensions. The cartesian base schemes
need not be affine or separated. Surjectivity is used only for reflection
of the all-fibres condition. Nonaffine dimension locality, constructibility
and unrestricted filtered descent over original rings remain separate
obligations of the parent whole-paper task.
