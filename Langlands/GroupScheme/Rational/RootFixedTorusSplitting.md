# From fixed actual roots to a split maximal torus

All fields and group schemes in this module lie in an arbitrary universe `u`.
The results retain arbitrary characteristic.

For a semisimple group `G` over a field, a split closed torus `i : T → G`
and a root datum `P` of that actual inclusion,
`IsSemisimple.character_eq_of_fixed_roots` proves that an integral linear
endomorphism of the actual character lattice that fixes every actual root is
the identity on every character. The root index type may lie in an independent
universe. The statement uses the actual roots, including their supplied
root-datum identification.

The implemented proof uses `IsSemisimple.finite_quotient_rootSpan`. Fixedness
on the roots implies fixedness on their integral span, by including that span
in the kernel of the difference between the endomorphism and the identity.
Finiteness of the quotient puts a positive multiple of any character in the
root span. The character lattice of the split torus is torsion free: its
rationalization injects into a rational vector space. Cancellation of the
positive multiple therefore gives fixedness of the original character.
`character_eq_of_fixed_maximalTorus_roots` uses the published root-datum
existence theorem to remove the choice of root datum when `i` is maximal.

Now let `L/k` be a finite Galois extension, let `T_L` be split, and suppose
that every actual character of `T_L` is fixed by every `k`-automorphism of
`L`. For any split torus `S` over `k` and any supplied commutative-group-scheme
isomorphism `e : T_L ≅ S_L`,
`IsSplitTorus.descendIsoOfFixedCharacters` constructs an isomorphism `T ≅ S`
over `k`. It chooses an isomorphism supplied by the published finite Galois
character-equivalence descent theorem. The chosen ground-field isomorphism
is not asserted to have pullback equal to the supplied isomorphism `e`;
its character pullback is the one supplied to that descent theorem.

To check the descent input, use the additive character equivalence induced
by `e`. The ordinary Galois action on `T_L` characters is trivial by
hypothesis. Every character of `S_L` is the canonical pullback of a character
of the original split torus `S`, so the ordinary Galois action there is also
trivial. Thus the character equivalence is equivariant.

`IsSplitTorus.of_galoisFixedCharacters` chooses a split-torus presentation of
`T_L`, identifies the standard split torus over `L` with the base change of
the same standard split torus over `k`, and applies the preceding construction.
The resulting ground-field isomorphism proves that `T` is split over `k`.

Finally, `isSplitTorus_of_galoisFixed_roots` takes a group `G` over `k`, a torus
map `j : T → G`, and assumes that `G_L` is semisimple, `j_L` is a maximal
torus, `T_L` is split, and every actual root character of `j_L` is fixed by
every `k`-automorphism of `L`. Apply character rigidity to the actual integral
Galois endomorphism for each automorphism. Every character is fixed, so the
finite Galois splitting criterion gives `IsSplitTorus T.toGrp`.

This is an internal derived unit. Its inputs are finite root index,
torsion-free character lattices, actual root-datum existence and equivariant
finite Galois character descent. It supplies the step from fixed roots to a
split torus. It does not establish fixedness of the roots, existence of an
irreducible actual root system, a stable chamber, or the host local anisotropic
affine-diagram theorem.
