# Anisotropy of the actual finite-separable norm-one torus

Proof draft: Worker 1107. Submission preparation: Worker 1563.

`WeilGm.normOneAnisotropy` proves the proposition
`WeilGm.normOneAnisotropyStatement k K` from the statement module
`Torus.WeilRestrictionNormOneAnisotropyStatement`.
The fields `k` and `K` lie in an arbitrary common universe, with a specified
algebra structure and finite dimension. Separability is the explicit
premise. The conclusion is split rank zero for the actual determinant-norm
kernel, with all characteristics and degrees, including degree one,
retained.

## Proof as implemented

The proof first applies the internal helper
`isAnisotropic_of_cocharacter_eq_zero` from `Torus.CocharacterAnisotropy`.
It remains to show that every actual ground-field cocharacter of the
commutative norm-one group scheme is zero.

Choose an algebraic closure of `k`. Its normality and the fact that every
polynomial splits meet the coefficient-field hypotheses of the published
`WeilGm.normOneGaloisFixedLattices`. The cocharacter clause of that theorem
says that every Galois-fixed geometric cocharacter is zero.
The canonical base change of a ground-field cocharacter is Galois-fixed,
by `cocharacterLattice.galoisRepresentation_baseChange`.
It is therefore zero over the algebraic closure. The published
`cocharacterLattice.algebraBaseChange_injective` reflects this equality
back to the ground field.

The helper completes the comparison with actual split subtori. A
coordinate cocharacter of any nonempty finite split torus vanishes after
its closed inclusion into the norm-one group. Cancellation through that
inclusion makes the coordinate cocharacter zero. Its matching projection
would then make the identity of the multiplicative group zero,
contradicting `gmEndEquiv k`, which sends these maps to `1` and `0` in
the integers. Thus every closed split torus has empty index type, and
`isAnisotropic_iff` gives split rank zero.

All equalities are equalities of actual group-scheme homomorphisms or
subgroup functors on all test schemes. The proof neither assumes
ground-field cocharacter vanishing as a final premise nor uses
surjectivity of descent onto fixed cocharacters.

## Provenance and scope

This is the internal derivation documented in the paired statement
Markdown. The norm-one construction, the Galois fixed-lattice theorem,
and the canonical base-change maps and injectivity are existing
published constructions and proofs. The coordinate-cancellation helper
is proved in the accompanying module. The short ground-field vanishing
argument also appears in Worker 1107's separately shared rational-lattice
proof draft; this module uses the published fixed-lattice and base-change
theorems directly and does not depend on that draft.

The statement Markdown records the Borel–Tits rank-zero convention and
its distinction from Milne's no-noncentral-split-torus convention. This
proof uses the existing `IsAnisotropic` predicate exactly. It makes no
assertion about finite separable product algebras, general cocharacter
descent surjectivity, rational-point quotients, or integral models.
