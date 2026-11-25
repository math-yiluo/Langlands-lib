# The actual split-central mass and normalization of packet preimages

The group-Levi orbit-packet central projection formula carries the factor
`muA(A_G(F) ∩ G¹)` when the central Haar measure is arbitrary. This
derived module supplies its positivity and finiteness and the corresponding
preimage normalization in the lower inclusion of Waldspurger VIII.4.2,
printed p.330 (PDF p.96). It changes no Haar measure.

`rationalSplitCentralMass` is the real value of that literal mass, measured
inside the actual split-component point image. The published compactness
of its intersection with the common norm kernel in the ambient group,
transported through the subgroup embedding, proves compactness inside
the central subgroup. The common norm kernel is open and contains the
identity. Its preimage is therefore nonempty and open, so every Haar
measure assigns it strictly positive mass. Compactness makes that mass
finite. Its real value is consequently strictly positive and its complex
coercion is nonzero.

`mem_rationalCuspidalCentralImage_of_mass_smul` assumes an actual cuspidal
Schwartz function whose actual central projection is this mass times
a specified function. It multiplies the same Schwartz function by the
reciprocal of the nonzero complex mass. The cuspidal submodule is stable
under scalar multiplication, and scalar multiplication commutes with the
literal central integral without a convergence or interchange premise.
The resulting vector is an actual raw central preimage of the desired
function, with the original central measure.

This module proves neither the existence of the required cuspidal packet
nor either of the closed targets `RationalCuspidalDiscreteCoefficientStatement`
and `RationalCuspidalFixedCoefficientLiftingStatement` (module
`RationalCuspidalCentralStatements`). Prescribed-value section extension,
the actual group-Levi packet comparison and packet cuspidality are
separate lower-inclusion obligations, not treated here.
