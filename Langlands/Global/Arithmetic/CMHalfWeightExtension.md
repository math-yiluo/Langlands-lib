# Quotient extension for conjugate-inverse Hecke characters

This internal helper assembles an actual Hecke character from explicit arithmetic
compatibility data. It is part of the proof of the weight-one existence
proposition. It does not supply the arithmetic data or assert their existence.
The construction follows from the general complex-character extension theorem
in `Langlands.Topology.ComplexCharacterExtension`.

For a number field `K`, `classQuotientMap N` is the continuous quotient map from
the actual idele-class group to its quotient by a subgroup `N`. No closedness
assumption on `N` is needed.

For a CM field, `exists_heckeCharacter_of_open_kernel` assumes that `N` contains
every class `x c(x)` and every integral local class at the places of a finite set
`S`. It also assumes an open subgroup `H` of the actual ideles, containing the
whole archimedean factor, and a continuous archimedean character `η`. The precise
compatibility requirement is that `η` of the infinite projection is one on each
element of `H` whose idele class lies in `N`.

The implemented proof restricts the composition of the class map and the
quotient map to `H`. Both quotient maps are open, and restriction to the open
subgroup preserves openness. The compatibility condition is exactly the kernel
condition for descending `η` from `H` along this map. The general extension
theorem supplies a continuous complex-unit character on the full quotient.
Pulling it back to idele classes gives the Hecke character.

Triviality on `N` proves the three conclusions. Killing `x c(x)` gives inversion
under the actual arithmetic CM involution. Agreement on `H`, together with
containment of all infinity ideles, gives the prescribed infinity character.
Killing the integral local classes gives unramifiedness at every place of `S`.
The theorem places no extra conditions on `S`; conditions needed to produce
`H`, `N`, and the compatibility proof remain separate arithmetic obligations.
