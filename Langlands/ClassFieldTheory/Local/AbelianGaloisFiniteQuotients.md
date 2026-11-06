# Finite quotients of the actual abelianized absolute Galois group

Worker 1651 develops this internal topological Galois adapter for profinite
reciprocity. It uses the existing actual Galois and closed-commutator quotient
constructions. It asserts no reciprocity or norm-residue theorem.

For any perfect field `K` in an arbitrary universe and any open subgroup `U` of
`Field.absoluteGaloisGroupAbelianization K`, `fixingGroup` takes the inverse
image under the actual quotient projection. Its fixed field `fixedField` is
finite over `K` because the subgroup is open, and Galois because it is normal.
The subgroup contains the commutator, so its quotient and the Galois group of
the fixed field are commutative. `extension` therefore packages an actual
`FiniteAbelianExtension K`, in the original chosen algebraic closure.

`extension_ker` proves that its finite restriction, descended from the absolute
Galois group, has kernel exactly `U`. It compares subgroup inverse images
under the surjective abelianization projection and uses the infinite Galois
fixed-field correspondence. `abelianRestriction_surjective` lifts an arbitrary
finite automorphism to the algebraic closure and then projects to the
abelianization. `quotientEquiv` is the resulting continuous multiplicative
isomorphism from the actual quotient by `U` to the actual finite Galois group.
Both sides are discrete. Its value on a quotient representative is definitionally
the existing finite restriction, as recorded in `quotientEquiv_mk`.

The provenance is internal and derived: the definitions specialize Mathlib's
infinite Galois correspondence and group quotient universal property to the
published `Langlands.LocalClassField` constructions. In particular, this is
an adapter needed to compare finite abelian field restrictions with all open
finite quotients of the actual profinite Galois abelianization. No arithmetic
class formation, local Artin map, chosen Frobenius lift, additional field
hypothesis beyond perfectness, or reciprocity existence premise is used.
