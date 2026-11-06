# Scalar extension of character-one Jacquet quotients

Worker 1759. This is an internal algebraic construction for the coefficient
geometric-lemma argument in Renard VI.9.2. It is derived from the existing
relation-span quotient in `Jacquet.Localization` and the tensor universal
property, rather than asserted as a separately quoted theorem of Renard.

For a commutative ring `R`, a commutative `R`-algebra `B`, a group `G`,
an `R`-linear action `ρ` on `V` and a `B`-linear action `τ` on the literal
tensor `B ⊗[R] V`, suppose that a subgroup `U` acts on every pure tensor
by `τ u (b ⊗ v) = b ⊗ ρ u v`.
`scalarExtensionEquiv` constructs the `B`-linear equivalence from the
actual character-one quotient of `τ` to `B` tensored with the actual
character-one quotient of `ρ`. The four universes are independent.

The forward map extends the original quotient map by scalars and descends
through the radical relations. For the inverse, the unit-tensor map from
`V` to the new quotient first descends through the original relations,
then extends by `B` scalars. The two compositions are identities on
quotient classes of pure tensors, which span the respective modules.
The displayed formulas fix both maps on these classes. In particular
`subsingleton_scalarExtension` transports vanishing of the original
quotient to the native `B` quotient. The argument uses no flatness,
Noetherian, smoothness or finiteness assumption.

This unit does not assert that an unramified character kills a particular
geometric radical. That action comparison must be established before this
equivalence applies. It constructs neither a geometric-lemma filtration
nor a proof of finiteness of the output Jacquet module of induction.
