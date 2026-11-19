# Continuous unit corestriction in a common Galois field

Let \(\Omega/K\) be Galois and let \(E\) be a finite intermediate
field. The continuous action of \(\operatorname{Gal}(\Omega/E)\)
on the discrete units of \(\Omega\) identifies with the restricted
action of the Krull fixing subgroup of \(E\). The group map is
restriction of scalars, and the coefficient map is the identity
on units.

`intermediateUnitCorestriction` uses the actual continuous
cohomological transfer from this open fixing subgroup.
The Library's index identity gives the composition of
restriction followed by corestriction. The fixing subgroup index
is the degree \([E:K]\), so that composition is multiplication
by \([E:K]\). Each finite normal quotient stage computes the
same transfer under the finite-stage comparison.

This transports the cohomological transfer and its degree identity
used in Serre, *Local Fields* (1979), Chapter XI, §2, Proposition 1,
printed pp. 167–168, to the Library's actual Galois unit modules.
In particular \(\Omega\) can be the separable closure of \(K\) in
any characteristic.
