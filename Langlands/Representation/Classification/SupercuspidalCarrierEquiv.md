# Changing the carrier universe of supercuspidal classes

For a p-adic field `F` with topological data `T` and a rank `n`,
`PadicField.TopologicalData.supercuspidalClassCarrierEquiv T n` identifies the
supercuspidal class spaces of the same group `GL_n(F)` in any two carrier
universes. The field and its topology are fixed. Each class space is the
quotient by isomorphism of actual irreducible smooth supercuspidal
representations.

The construction applies `padicIrreducibleSmoothSmallRealization` to the
underlying smooth representation. It packages the result as a supercuspidal
object using `GeneralLinear.isSupercuspidal_of_equiv`, which carries
admissibility and Jacquet vanishing across the intertwiner. For isomorphic
source objects, composition with the chosen intertwiners gives isomorphic
target objects. This descends to the quotient. Performing the construction
in the reverse direction and composing the intertwiners gives an inverse on
classes.

`supercuspidalClassCarrierEquiv_isoClass_eq_iff` characterizes the bijection
without reference to the chosen models. It matches two classes exactly when
there is a linear intertwining equivalence between their representatives.
`isUnitarizable_supercuspidalClassCarrierEquiv_iff` follows by transporting
an invariant positive Hermitian form along that equivalence.

The construction is derived from the Library's
[small realization theorem](../Smooth/SmallRealizationProof.md) and
[supercuspidal class definition](Supercuspidal.md). It permits the integral
supercuspidal lattice in Henniart's composite map to be formed at independent
carrier universes. Henniart describes the map in §§3.7–3.8, printed p. 451 of
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
