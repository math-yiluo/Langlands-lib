# Full faithfulness of equivariant change from étale to quasi-étale sheaves

`Langlands.Sheaf.Equivariant.Analytic.EquivariantEtaleToCompactProbeStatement`
states that the unit `F ⟶ μ_* μ^* F` is an isomorphism for module sheaves
on the equivariant étale site of a `G`-space `X`. The acting group is
a topological group, and its quotients by open subgroups are `v`-small.
This size condition fits the coset-indexed induction spaces of Theorem
1.4.2 in the geometric universe. The unit isomorphism implies full faithfulness
of the inverse image by the adjunction criterion. The site functor defining
`μ : X(G)_qét → X(G)_ét` is the inclusion of equivariant étale test objects
into equivariant quasi-étale test objects.

The source is Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
Corollary 1.4.3, printed and PDF p. 10, with the morphism of sites and the
inverse-image formula on p. 3, §1.2. The statement is for the unit clause of
the corollary. Its application to values on quasi-étale test objects also
compares with global sections of the original étale sheaf pulled back to
that test space. The retained manuscript is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
PDF SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
within registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
[Author's manuscript](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=10)

The action is over a fixed complete ultrametric normed field `K`. The
objects of the two equivariant sites are Hausdorff and their actions are
continuous in the analytic sense of `GSpace`. In particular, the comparison
`compactProbeQuasiEtaleHausdorffComparison` identifies chart-neighbourhood
covers with the compact-probe covering rule on the underlying quasi-étale
objects. Equality of the two equivariant topologies follows, so continuity
of the inclusion follows from `quasiEtaleToEtale`.

The pushforward is restriction of the underlying presheaf. The inverse
image is constructed by left Kan extension of that presheaf along the
opposite inclusion, followed by sheafification. The sheafification and Kan
extension exist for modules over a commutative ring `R` at the universe
`max u (v + 1) z uR`, where the field has universe `u`, analytic spaces
have point and chart universes `v`, and `G` has universe `z`. The module
unit is the map of the constructed adjunction. The proposition states
its invertibility under the stated size condition.
