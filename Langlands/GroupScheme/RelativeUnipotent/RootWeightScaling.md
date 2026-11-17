# Positive integral scaling of actual root-weight filtrations

This derived auxiliary construction works over an arbitrary commutative ring, with any supplied root-height chart and nonnegative secondary root weights satisfying the all-test commutator bound. It introduces no geometric existence assumption.

`RootWeightData.scale q hq` multiplies every secondary weight by a positive natural number `q`. The commutator bound follows because multiplying both generator weights and the cutoff by `q` leaves the actual generated subgroup unchanged. The proof unfolds the supremum of retained root factors and cancels the positive multiplier in each inequality.

`scale_subgroup_zero` proves equality of the actual positive subgroup functors on every scheme test, including zero weights and empty families. More generally, `scale_subgroup` identifies scaled term `q * (d + 1) - 1` with original term `d`, since term indices are one less than their positive cutoffs. `scaleTermIso` compares the actual representing group schemes at those indices; its composite with the original inclusion equals the scaled inclusion.

These statements allow a positive integral realization of a face-height functional to be used without changing the stored unscaled filtration. They do not assert that arbitrary integral weights are realized by a cocharacter, nor construct a global relative filtration.

Provenance: internal derivation from the definitions of generated root-weight subgroups and uniqueness of their supplied representatives.
