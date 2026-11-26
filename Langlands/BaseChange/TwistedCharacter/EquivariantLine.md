# Twisted character lines and central characters under transport

These internal lemmas use the Library's representation twists, central
characters and twisted character distributions. They support the
fixed-central-character construction of Henniart–Lemaire (2011), II.5.13,
proof, printed p. 113, without identifying distinct choices of intertwiners.

## `center_le_ker_of_equiv_twist_same_centralCharacter`

Let `ρ` be a representation on a nonzero complex vector space with central
character `χ`. If `π` has the same central character and is equivalent to
`twist ψ ρ`, then `ψ` is trivial on the centre. Indeed, equivariance transports
the action through `χ` to `twist ψ ρ`, on which a central element `z` also
acts by the scalar `ψ(z)χ(z)`. Apply both scalars to a nonzero vector, then
cancel that vector and the unit `χ(z)`. Neither irreducibility nor
unramifiedness is required.

## `exists_twistedDistribution_eq_smul_of_equiv`

Let `e : ρ ≅ π` be an equivalence of admissible representations of a
Hausdorff, locally compact, totally disconnected topological group with its
Borel sigma-algebra. Assume `ρ` is irreducible. For a group automorphism
`θ` and isomorphisms `A : ρ ≅ ρ ∘ θ` and `A' : π ≅ π ∘ θ`, the twisted
distribution of `(π, A')` is a complex scalar multiple of that of `(ρ, A)`
for the same left-invariant measure finite on compacts. The statement does
not require `e` to commute with the chosen twisting operators.

The proof transports `A'` to `B = e⁻¹ A' e` on `ρ`, where the final map in the
composition is the equivalence between the precomposed representations.
Then `A⁻¹ B` is an untwisted endomorphism of `ρ`, so
`admissibleSchur_scalarEndomorphism` makes it a scalar `a`. Thus `B = a A`.
Apply `twistedDistribution_eq_of_equivariant` using `e⁻¹` and then
`twistedDistribution_smul`. This is the distributional version of the
Schur argument for the scaling of intertwiners in HL II.5.2–II.5.3,
printed pp. 101–102; the Lean lemma asserts proportionality, not equality
of the twisted distributions or an isomorphism of the twisted pairs.
