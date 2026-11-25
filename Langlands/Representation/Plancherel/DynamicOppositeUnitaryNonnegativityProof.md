# Nonnegativity of the canonical opposite-intertwiner scalar

`Langlands.Plancherel.conditionalDynamicOppositeUnitaryNonneg` proves
`ConditionalDynamicOppositeUnitaryNonnegStatement.{u, uV}`. The canonical
composition scalar `j_P` is regular with a nonnegative real value at every
unitary unramified character in `p.regularRegion ∩ q.regularRegion` for the
supplied forward and reverse continuations. [Published target](DynamicOppositeUnitaryNonnegativity.md)

The theorem applies `conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction`
to the published `conditionalDynamicOppositeHermitianAdjunction`. The reduction
uses `_hdag` on the nonempty open forward convergence set to apply the adjunction
at `z` and its conjugate inverse `z†`. It extends the identity by clearing the
continuation denominators and applying the identity principle to regular
functions. At a unitary parameter `z† = z`. The reduction extracts the canonical
scalar with a nonzero compact-picture vector `e` and the functional
`⟨e, ·⟩_P / ⟨e, e⟩_P`. The adjunction gives its value as
`⟨J e, J e⟩_{P̄} / ⟨e, e⟩_P`, where `J` is the forward continued operator and
the two forms come from an invariant positive form on the inducing
representation. [Reduction](DynamicOppositeUnitaryNonnegativity.md)
[Hermitian adjunction](DynamicOppositeHermitianAdjunctionProof.md)

The type retains the structural premises, both compact factorizations and
Levi splittings, unitarizability, the continuation data, the nonempty open
convergence sets and generic irreducibility. The field and representation
carrier universes are independent.

The squared-norm identity is the step in the proof of IV.3 (6), printed
p. 287 (PDF p. 53), following the construction of `j_P` in IV.3, printed
p. 285 (PDF p. 51), and the adjunction IV.1 (11), printed p. 283 (PDF p. 49).
The Library records this as a derived common-regular-point result. The
source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
registered as `waldspurger-2003-plancherel`, PDF SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[Original article](https://doi.org/10.1017/S1474748003000082)
