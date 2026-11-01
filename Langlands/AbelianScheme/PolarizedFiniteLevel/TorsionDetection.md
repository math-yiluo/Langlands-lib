# Detection of actual torsion-scheme morphisms

This internal support construction proves global torsion detection for the
existing ordered full-level structures. It uses the actual torsion kernel and
the existing abelian-scheme and full-level definitions. Its provenance is the
published APIs and Mathlib's unramified-diagonal and equalizer geometry; it
does not formalize an additional assertion from the moduli literature.

The private unramified extensionality lemma uses the open diagonal of a
formally unramified morphism locally of finite type. The equalizer of two maps
over the base is its base change, hence an open immersion. Every source point
admits a geometric point obtained from an algebraic closure of its residue
field. Agreement at all such points makes the equalizer surjective, so it is an
isomorphism. This requires no connectedness, reducedness or noetherianity of
the base.

`FullLevel.torsionMap_ext` uses the published `torsionFiniteEtale` theorem
for the target abelian scheme and a positive invertible order. The
`FullLevel.fibreLevelMap_ext` lemma from `FibreDetection` and
`kernelLevelEquiv_map` identify the actions on geometric points of the actual
torsion kernel. The unramified extensionality lemma then proves equality of
the actual torsion-kernel maps. The hypotheses are agreement on the ordered
global sections, positivity of the order, and invertibility of that order
in the global sections of the base.

`PolarizedIso.torsionIso` constructs an isomorphism in the actual slice
category over the base. Its forward and inverse maps are `kernelLevelMap`
applied to the homomorphism and inverse of the given abelian-scheme
isomorphism. To verify the inverse equations, the proof cancels the
monomorphic kernel inclusion, uses `kernelLevelMap_ι`, and applies the
inverse equations of the original isomorphism. This construction itself
requires neither positivity nor invertibility of the order.

At a positive invertible order, `PolarizedIso.torsionIso_eq` uses
`FullLevel.torsionMap_ext` and the level equations to show that any two
polarized isomorphisms carrying the ordered sections induce the same actual
torsion isomorphism. The identity construction is checked directly in
`PolarizedIso.torsionIso_refl`. Comparing an automorphism with the identity
gives `PolarizedIso.torsionIso_eq_refl`: an automorphism preserving the
ordered level is the identity on the actual torsion scheme.

These results do not prove equality of the original abelian-scheme
homomorphisms or automorphisms, a faithful action on one finite level, or
the moduli representability theorem.
