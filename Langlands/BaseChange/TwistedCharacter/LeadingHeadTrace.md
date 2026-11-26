# A nonzero leading coefficient for a twisted head character

`TwistedHeadLeadingCoefficientStatement` concerns an admissible
finite-length twisted pair with an admissible irreducible head. The
group is locally compact, Hausdorff and totally disconnected with its
Borel structure. The measure is left invariant and finite on compact
sets. Let `L` be a subspace containing the twisted traces of the
irreducible subquotients of the head kernel, for every twisting
isomorphism of each admissible subquotient. Suppose the twisted trace
of the head for the supplied isomorphism lies outside `L`.

Adjoin the line of the twisted trace of the whole representation to `L`.
The proof `twistedDistribution_sub_smul_head_mem` puts the head trace
in this larger subspace by
`twistedDistribution_mem_of_irreducibleHead`. It thus equals a vector in
`L` plus a scalar multiple of the whole trace. The scalar is nonzero by
the assumption on the head trace. Dividing by it expresses the whole trace
as a nonzero multiple of the head trace modulo `L`.

This yields the leading-term expression for the twisted standard traces
used in Henniart–Lemaire (2011), II.5.10–II.5.11, once independence
separates the head line from the traces of its lower-rank constituents.
