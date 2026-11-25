# The actual Borel parameter scheme inside a parabolic parameter scheme

This internal construction implements the open and closed restriction in the
proof of Conrad, *Reductive group schemes* (2014), Theorem 5.2.11(3), p.158.
The clopen Borel-locus statement remains an explicit premise.

For a parabolic family `j` in the base change of a reductive group to a supplied
parameter scheme `M`, `borelParameterOpens` equips the set of Borel residue fibres
with the open-subset structure provided by that premise. `borelParameter` is
the actual associated open subscheme, viewed over the original base. It uses
`TorusSubgroupModuli.openParameter`, whose inclusion and factorization properties
are proved in the paired `HomScheme/OpenParameterFamily` module.

`smooth_borelParameter` and `isProper_borelParameter` transfer smoothness and
properness from the supplied parameter scheme. The second proof uses the
closedness part of the same clopen premise. These claims hold over every scheme
in universe `u` and do not assert existence of the supplied parabolic family.
