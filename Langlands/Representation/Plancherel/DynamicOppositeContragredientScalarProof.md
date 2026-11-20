# Contragredient compatibility of the canonical opposite-intertwiner scalar

`Langlands.Plancherel.conditionalDynamicOppositeContragredientScalar` proves
`ConditionalDynamicOppositeContragredientScalarStatement.{u, uV}`. The
canonical composition scalar for `A.contragredient` is the pullback of
the scalar for `A` along `z ↦ z⁻¹`, as an equality in the rational function
field of unramified characters. [Published target](DynamicOppositeContragredientScalar.md)

The theorem applies `conditionalDynamicOppositeContragredientScalar_of_dualAdjunction`
to the published `conditionalDynamicOppositeDualAdjunction`. The reduction
continues the two directions of the bilinear adjunction from the supplied
open convergence sets by clearing denominators and using the identity
principle. It chooses compact-picture vectors for `A` and `A.contragredient`
with nonzero pairing and uses that pairing to normalize the scalar-extraction
functional on each side. Applying both adjunctions to the composition
identifies these coefficients at inverse parameters. The cross-multiplied
difference vanishes after multiplication by the product of the four
continuation denominators, with the two for `A` pulled back by inversion.
Cancellation in the domain of regular functions gives the fraction field
identity.
[Reduction](DynamicOppositeContragredientScalarReduction.md)
[Dual adjunction](DynamicOppositeDualAdjunctionProof.md)

The type retains the structural premises, both compact factorizations and
Levi splittings, and separate continuations and nonempty open convergence and
generic irreducibility sets for `A` and `A.contragredient`. It also retains
`_hinvForward` and `_hinvReverse`, which send the chosen forward and reverse
open sets for `A` into the opposite full convergence domains for
`A.contragredient` under parameter inversion. The field and representation
carrier universes are independent.

This is the opposite-pair form of Waldspurger's IV.3 (2), printed p. 286
(PDF p. 52), which follows from IV.1 (11), printed p. 283 (PDF p. 49). The
source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
registered as `waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[Original article](https://doi.org/10.1017/S1474748003000082)

Worker 228, Task 7228.
