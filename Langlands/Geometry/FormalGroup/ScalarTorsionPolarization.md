# Cartier duality and polarizations on scalar-power kernels

Rapoport and Zink, *Period Spaces for p-divisible Groups* (1996),
§3.20–3.21, printed pp. 80–82 (PDF pp. 94–96), use an antisymmetric
polarization and require integral polarization isomorphisms in their
PEL moduli problem. Harris, *Supercuspidal representations in the
cohomology of Drinfel'd upper half spaces* (1997), Appendix, printed
p. 113 (PDF p. 39), specifies an order-antilinear polarization
isomorphism for the formal module in condition (ii).

`TorsionCartierDuality` expresses integral Cartier duality on the actual
represented scalar kernels. At exponent \(n\) it identifies the
additive points of the first kernel with all relative characters of the
second kernel, by a natural isomorphism on scheme tests. Inclusion on
the first kernel corresponds to pullback of characters along the
second kernel's scalar transition. Evaluation gives a bilinear,
test-natural pairing with that adjointness law.

`TorsionPrincipalPolarization` specializes the duality to one formal
module and requires the pairing to invert when its arguments are
exchanged. The reverse adjointness law follows from this
antisymmetry. `OrderAction.IsAntilinearTorsionPolarization` uses the
given algebra involution and the actual torsion scheme maps of the
order endomorphisms. It requires composition by an endomorphism in
the first variable to equal precomposition of the relative character
by the involuted endomorphism. The pointwise adjointness law follows
by evaluation.

The construction applies to scalar-divisible finite-coordinate formal
modules over affine coefficient bases. For the \(p\)-divisible
polarization condition the scalar is \(p\). Duality here is an
isomorphism to the actual relative character functors.
