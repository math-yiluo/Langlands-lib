# Local dimension under flat locally quasi-finite morphisms

This internal supporting result supplies the local-dimension step in the
comparison of Lie dimensions under smooth group-scheme isogenies. It is derived
from the imported Mathlib going-down, quasi-finite incomparability and
prime-height APIs; it does not introduce a new geometric hypothesis for that
consumer.

`ringKrullDim_eq_of_flat_quasiFinite_local` states that a flat quasi-finite local
algebra between commutative local rings has the same Krull dimension as its
base. The rings may inhabit different universes. The algebra map is explicitly
assumed local. No noetherian or finite-dimensional assumption is needed.

The private height lemma proves that each prime of the target has the height
of its contraction. Quasi-finite incomparability makes contraction strictly
monotone on prime spectra. Flat going down lifts every strictly smaller prime
of the base beneath a given target prime. `Order.height_eq_of_strictMono` then
gives equality of heights. Apply this equality to the target maximal ideal;
locality identifies its contraction with the base maximal ideal, and the
maximal-ideal height formulas identify their heights with Krull dimensions.

`stalk_ringKrullDim_eq_of_flat_locallyQuasiFinite` applies the algebraic result
to the actual stalk homomorphism of a flat locally quasi-finite scheme map at
any source point. Its algebra structure is the one induced by that stalk map;
locality comes from the locally ringed space morphism, flatness from
`Flat.stalkMap`, and quasi-finiteness from `Scheme.Hom.quasiFiniteAt`.
The equality compares the source stalk at the chosen point with the target
stalk at its image. It does not assert an equality of tangent dimensions for
singular schemes. Smoothness and regularity enter separately in the intended
Lie-dimension application.
