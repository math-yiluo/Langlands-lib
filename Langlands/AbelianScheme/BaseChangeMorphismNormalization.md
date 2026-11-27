# Normalization of an abelian-scheme morphism lift

`exists_hom_of_baseChange_scheme_lift` takes two actual abelian schemes over
`S`, a base morphism `T ⟶ S`, a homomorphism of the base changes, and a
scheme morphism over `S` reducing to that homomorphism. It produces an
abelian-scheme homomorphism over `S` with the same reduction.

The construction `normalizeSchemeMorphism` evaluates a scheme morphism on
the zero section and translates its value back to zero. The translated map
preserves the zero section, so `pointedMorphismRigidity` makes it a
homomorphism. The point that is
translated back is zero on the actual base change, by naturality of the
unit section and because the reduced morphism is a group homomorphism.
The base-change formula for translation gives the required equality at
the first projection, and the second projection equality holds because
both maps are over `T`.

This is the normalization in Kai-Wen Lan, *Arithmetic compactifications
of PEL-type Shimura varieties*, revised 14 March 2021, Corollary 2.2.2.2,
printed p. 144 (PDF p. 172). The construction applies to any base morphism
when a scheme lift is supplied. The source uses this argument for a closed
immersion with nilpotent ideal. The retained source is
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
