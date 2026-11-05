# Closed immersion of proper maps detected on relative base fibres

This internal derived unit uses the actual relative fibre morphisms of
`ProperFibreClosedImmersion`. All schemes lie in an arbitrary common
universe. The base map is arbitrary.

For a morphism surjective on stalks, the map on actual residue fields is
surjective: its composite with the residue quotient is the residue
quotient composed with the stalk map. Both maps in the latter composite
are surjective. Injectivity of a homomorphism of fields then gives the
actual residue-field isomorphism
`residueFieldIsoOfSurjectiveOnStalks`. Its forward map is exactly the
original residue-field map. The resulting isomorphism instance has low
priority.

If a Cartesian change induces an isomorphism of residue fields at a
point, the induced square between target residue fibres has isomorphisms
on both horizontal sides. Its actual arrow isomorphism identifies the
two closed-immersion conditions.

The main criterion says that a proper map `f : X ⟶ Y` is a closed
immersion if and only if, for every point `s` of any base `S` of `Y`,
the actual induced map from the fibre of `f ≫ q` to the fibre of
`q : Y ⟶ S` is a closed immersion. The forward direction is stable
base change. For the converse, a point `y` of `Y` has its canonical
point in the fibre of `q` over `q y`. The fibre inclusion is a
preimmersion, hence surjective on stalks, and therefore gives the
residue-field isomorphism just constructed. The preceding invariant
criterion transfers closed immersion from the target residue fibre of
the relative map to the target residue fibre of `f` at `y`. The
proper target-residue-fibre criterion then proves that `f` is a closed
immersion.

The proof uses the finite-module support and Zariski Main Theorem
argument already implemented in `ProperFibreClosedImmersion`. It adds
no flatness hypothesis. It does not supply cubic generation, finite
local rank of a direct image, fibre very ampleness, or moduli
representability.
