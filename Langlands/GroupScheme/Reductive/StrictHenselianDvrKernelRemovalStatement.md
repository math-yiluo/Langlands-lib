# Removing the closed-fibre kernel over a strictly Henselian DVR

Worker 685.

`Langlands.GroupScheme.StrictHenselianDvrKernelRemovalStatement.{u}` is an
unproved proposition for every universe `u`. Let `R` be a strictly Henselian
discrete valuation ring: it is a commutative domain with instances
`IsDiscreteValuationRing R`, `HenselianLocalRing R`, and
`IsSepClosed (IsLocalRing.ResidueField R)`. Let `G` and `H` be reductive group
schemes over `Spec R` and let `f : G ⟶ H` be an isogeny on every
residue-field fibre.

The proposition asks for a reductive group scheme `Q` and homomorphisms
`q : G ⟶ Q` and `g : Q ⟶ H` such that:

- `q` is an isogeny: its underlying scheme map is finite, flat, and surjective;
- `q ≫ g = f`;
- `g` is an isogeny on every residue-field fibre; and
- the base change of this particular `g` to `IsLocalRing.ResidueField R` is an
  isomorphism in the category of group schemes.

Both the input fibre hypotheses and the output fibre assertions use actual
base changes of the specified homomorphisms. The special fibre uses the
canonical quotient algebra structure on `IsLocalRing.ResidueField R` and
`Spec.algebraMap`. No abstract isomorphism of the source and target replaces
the assertion about `g`.

This is a derived intermediate assertion extracted from Brian Conrad,
*Reductive group schemes* (2014), Proposition 6.1.10, the proof from printed
p.192 to the first paragraph of p.193. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Conrad first takes the unique open and closed finite subgroup of `ker f`
whose special fibre is all of the special-fibre kernel, using EGA IV4
18.5.11(a),(c). It is flat, and normality in `G` follows from uniqueness and
the relative schematic density of sections of the split reductive group.
The represented finite locally free normal quotient, cited there from SGA3
V, then gives `q : G ⟶ G/H'` with reductive target and finite fppf quotient
map. The induced map `g` has trivial closed-fibre kernel.

The output fibrewise isogeny assertion makes explicit the property retained
when Conrad replaces `G` by that quotient. On every field fibre, surjectivity
of `g` follows from surjectivity of its composite with `q`. Finiteness and
flatness descend from that composite along the finite faithfully flat `q`.
This assertion does not include the
subsequent root-data rigidity argument proving that `g` is an isomorphism on
the generic fibre, nor the passage from arbitrary bases to this local base.
No proof of the intermediate assertion is supplied in this module.
