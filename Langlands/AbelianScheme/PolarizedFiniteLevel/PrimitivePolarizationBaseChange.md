# Base change of primitive dual-valued homomorphisms

Let `b : T ⟶ S` be a morphism between connected, locally noetherian
schemes on which every positive integer is invertible in global sections.
Choose a point of `T` with values in an algebraically closed field and
use its composite with `b` for `S`. Assume the published
`TorsionFiniteEtaleStatement`. The statements hold in every universe of
the underlying abelian schemes.

For an actual abelian-scheme homomorphism `f` over `S`,
`Tate.exists_nsmul_eq_baseChange_iff` shows that a positive integer divides
the pulled-back homomorphism exactly when it divides `f`. The proof uses
`Tate.exists_nsmul_eq_iff_levelMap_eq_zero` on the two bases to rephrase
divisibility by `k` as vanishing on geometric `k`-torsion. The finite
torsion base-change equivalences on the source and target intertwine
those restrictions. Surjectivity on the source and injectivity on the
target give the two implications.

Primitivity is equivalent to having no integer divisor greater than one.
In particular the zero homomorphism admits the divisor two, which
accounts for the zero-multiplier case of `Tate.IsPrimitiveHom`.
This gives `Tate.isPrimitiveHom_baseChange_iff`. Postcomposition by an
actual isomorphism also preserves and reflects primitivity because
composition by the inverse recovers the original divisibility equation.

The canonical changed-dual comparison in `DualWitness.pullbackMap`
is such an isomorphism. `DualWitness.isPrimitiveHom_pullbackMap_iff`
therefore applies the two results to an actual map into the chosen
dual. `DualWitness.pullbackPrimitiveRepresentative` uses this equivalence
to carry a primitive map whose positive multiple is the supplied
homomorphism to the corresponding primitive map over `T`. Additivity
of the canonical pullback preserves the same positive integer in the
multiple equation.

The constructions are internal consequences of the Library's finite
torsion divisibility criterion and dual base-change maps. They apply to
the primitive representatives of Harris polarization rays through their
existing multiple equation.
