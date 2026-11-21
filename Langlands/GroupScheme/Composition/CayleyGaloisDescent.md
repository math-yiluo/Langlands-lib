# Finite Galois twists of Cayley data

Let `L/K` be finite Galois, with `K` infinite of characteristic different from two. For a Cayley datum over `K`, `IsGaloisTwist P` says that each discrepancy `P σ(P)⁻¹` of a matrix in `GL₈(L)` preserves the extended unit and multiplication. `galoisTwist` constructs the Cayley datum over `K` obtained by transporting these operations and the norm to the basis given by `P`. The theorem `galoisTwist_isIsomorphismMatrix` certifies that `P` carries the descended unit and multiplication back to the original ones over `L`.

Each Galois conjugate of `P` differs from `P` by a Cayley automorphism on the left. Automorphisms preserve the norm, so the transported operations take Galois-fixed values on vectors over `K`. Descend their coordinates and use injectivity of the scalar inclusion to transfer the Cayley identities. The polar form of the descended norm is nonsingular because an element in its radical extends to one pairing trivially with an `L`-basis. The comparison with the original algebra follows by checking that `P` matches the units and the products of standard basis vectors.

This extends the coordinate descent in `CayleyGaloisTwist` to an arbitrary initial datum. It uses the coefficient extension and the intrinsic norm invariance of the Cayley datum.
