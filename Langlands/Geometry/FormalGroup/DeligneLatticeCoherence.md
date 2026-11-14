# Coherent inverse image of Deligne's graded and framed lattices

This module lifts the canonical identity and composition comparisons for ordinary
inverse image to the actual graded flat lattice and its full rational frame.
It constructs natural isomorphisms and proves their associativity and both unit
laws. The comparisons concern the existing inverse-image constructions, including
their actual homogeneous inclusions and frame, rather than supplied replacement
objects or preservation assumptions.

## Source and scope

The motivating source is V. G. Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed p.109 (PDF p.3), final paragraph defining the four
data `eta,T,u,r`, continuing on printed p.110 (PDF p.4). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
In that passage `eta` is a flat cyclically graded `O[Pi]`-sheaf and `r` is a full
rational frame in degree zero. The present coherence constructions are derived
categorical infrastructure for those data; they are not separately stated
results in the paper. In particular, they do not assert the special-formal-module
comparison of Proposition 2.4 in Section 2 B, printed p.110 (PDF p.4).

Lean permits a commutative ring `O`, a positive natural number `d` expressed by
`[NeZero d]`, and an element `pi : O`. The coefficient algebra is the existing
`PiAlgebra d pi`, with its relation `Pi^d = pi`. The bases are arbitrary topological
spaces and the maps are continuous. For framed objects, `F` is a field with an
`O`-algebra structure. All these types occupy the same universe. The categorical
results need no local-field hypothesis, nilpotence, injectivity of `O -> F`, or
nonvanishing condition on the image of `pi`.

## Actual graded lattices

`LatticePiSheaf.isoOfComponents` takes an actual total coefficient-sheaf
isomorphism `e`, actual isomorphisms `c_i` on every homogeneous component, and
forward inclusion squares

`c_i.hom ; inclusion_N(i) = inclusion_M(i) ; restrict(e.hom)`.

It derives the inverse inclusion squares by cancellation with the invertible
restricted total map, using functoriality and the inverse identities. The two
inverse equations reduce to those for the total sheaf. Thus it constructs a
genuine isomorphism in the existing category of lattices. The existing
`Hom.pi_naturality` applies, so the actual homogeneous Pi maps are preserved too.

Write `P_A(f)` for ordinary inverse image on sheaves of `A`-modules.
`LatticePiSheaf.inverseImageIdIso` uses `P_(O[Pi])(id) ~= Id` on the total sheaf
and `P_O(id) ~= Id` on each component. Its inclusion square follows from
naturality at the actual inclusion and the identity coherence for restriction of
scalars. `inverseImageIdNatIso` makes this comparison natural for every lattice
morphism.

For `f : X -> Y` and `g : W -> X`,
`LatticePiSheaf.inverseImageCompIso` has direction

`(M.inverseImage f).inverseImage g ~= M.inverseImage (g ; f)`.

It uses the ordinary comparison `P_A(f) ; P_A(g) ~= P_A(g ; f)` on the total
sheaf and every component. Its inclusion square follows from naturality at the
inclusion and composition coherence for the actual restriction comparison.
`inverseImageCompNatIso` proves naturality for every lattice morphism.

The two inclusion lemmas in the module display these squares explicitly.
The associativity and two unit laws follow by extensionality from the ordinary
inverse-image laws on the total coefficient sheaf. The first unit inserts the
identity on the original base and is the identity comparison pulled along `f`;
the second inserts the identity on the new base and is the identity comparison
of the pulled lattice.

## The full rational frame

`FramedLatticePiSheaf.isoOfLattice` takes an actual lattice isomorphism `e` and
the forward equation preserving the full rational frame. The inverse equation
follows by rationalizing the degree-zero inverse identity. Both inverse
identities then follow from the lattice isomorphism. No determinant-only
condition replaces preservation of the actual frame.

The existing frame on inverse image along `f` is the composite of the inverse
constant-sheaf comparison, `P_F(f)` of the original frame, and the rationalization
comparison. `FramedLatticePiSheaf.inverseImageIdIso_frame` proves that this frame
is carried to the original one by the rationalized degree-zero identity
comparison: rationalization identity coherence moves to the `F`-coefficient
identity comparison, naturality moves past the original frame, and constant-sheaf
identity coherence cancels the first comparison.

`inverseImageCompIso_frame` does the same for two successive inverse images.
Rationalization composition coherence combines the two rationalization maps
with the rationalized degree-zero composition map. Naturality of the
`F`-coefficient composition comparison moves it across the full original frame.
The inverse of constant-sheaf composition coherence then cancels the remaining
constant comparison. The resulting frame is exactly the frame on inverse image
along `g ; f`.

`FramedLatticePiSheaf.inverseImageIdIso` and `inverseImageCompIso` use these
proved equations to lift the lattice comparisons to framed isomorphisms.
Their natural-isomorphism versions are natural for every frame-preserving
morphism. Associativity and both unit laws reduce by framed-morphism
extensionality to the corresponding lattice laws.

This module supplies lattice and frame coherence only. Compatibility with the
ordinary-to-structural comparison and with `u`, full four-data coherence,
admissibility transport, the admissible Nilp functor, integral determinant
comparison, the normalized PGL action, comparison with special formal modules,
Proposition 2.4, and representability remain further obligations.
