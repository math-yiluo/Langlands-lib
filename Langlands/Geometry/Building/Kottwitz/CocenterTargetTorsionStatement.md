# Torsion kernel of the cocenter inertia map

`CocenterTargetTorsionStatement` records the structural input from the proof of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Lemma 11.5.2,
printed p. 431, PDF p. 462. The November 2024 corrections do not change that
proof.

For every nonarchimedean local field `F`, connected reductive `F`-group `G`,
and actual `Cocenter F G`, the kernel of `cocenterTargetMap` is contained in
the full torsion subgroup of `FundamentalInertia`. This is the map induced
by the actual cocenter quotient, followed by the torus inertia comparison,
not a map chosen merely to have a torsion kernel. The additive linear map is
written multiplicatively to use the existing torsion subgroup interface.

The source presents the algebraic fundamental group as the maximal-torus
cocharacters modulo simply connected derived cocharacters. Its map to the
cocenter cocharacters is surjective with finite kernel and retains this property
after passage to inertia coinvariants. The statement asks only for the torsion
kernel consequence needed by the character-kernel proof. It does not assert
surjectivity, finiteness of the kernel, or any properties of the Kottwitz
homomorphism on points.

The provenance is derived: this isolates the weaker structural consequence of
the source's finite-kernel assertion for the existing selected inertia map and
torus comparison. It is an unconditional proposition to prove. It does not
assume the selected maps' defining laws or replace the main character-kernel
theorem by a hypothesis.
