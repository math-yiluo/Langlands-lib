# Split-torus isogeny comparison on actual cocharacters

Worker 384 and Worker 1444.

`Langlands.GroupScheme.splitTorusIsogenyCocharacter` proves the exact published
proposition `Langlands.GroupScheme.SplitTorusIsogenyCocharacterStatement.{u}`.
For any field `k : Type u`, any two actual commutative group schemes `A` and `T`
over `Spec k` that are split tori, and any homomorphism `f : A ⟶ T` whose
underlying scheme map is finite, flat and surjective, the actual integral map
`RealTorusSpace.cocharacterMapInt f` is injective and has finite cokernel. Its
scalar extension to the rationals and the actual real map
`RealTorusSpace.cocharacterMapReal f` are bijective.

The proof works in arbitrary universe `u` and arbitrary characteristic. The
field need not be perfect, and no assumption is imposed on reducedness or
separability of the kernel. The target pair and every pair in its import closure
are used unchanged.

The supporting theorem `IsSplitTorus.exists_isogeny_quasiInverse` first produces
an actual homomorphism `g : T ⟶ A` and an integer `n ≠ 0` satisfying

`f ≫ g = n • 𝟙 A` and `g ≫ f = n • 𝟙 T`.

To construct it, the proof chooses splitting isomorphisms from `A` and `T` to
standard finite split tori `T_I` and `T_J`. Conjugating `f` gives the actual
standard-torus morphism `q`. Its underlying map remains finite, flat and
surjective because isomorphisms satisfy these properties and isogenies are
stable under composition. Flatness and surjectivity make that scheme morphism
an epimorphism.

The construction in `SplitTorusIsogenyQuasiInverse` now applies to `q`.
Its actual character pullback is injective by scheme epimorphy and has finite
cokernel by the finite-morphism comparison in `SplitTorusIsogenyCharacters`.
The elementary integer-module quasiinverse from
`SplitTorusIsogenyQuasiInverseLinear` is realized as an actual torus morphism by
summing its character columns followed by the coordinate cocharacters. This
gives both scalar composite identities on the standard tori. Transporting
this reverse morphism through the splitting isomorphisms gives `g` on the
original supplied group schemes; the two identities follow from associativity,
isomorphism cancellation and integer bilinearity of composition.

Finally, `SplitTorusIsogeny.cocharacter_isogeny_conclusions_of_quasiInverse` in
`SplitTorusIsogenyCocharacterLinear` applies directly to `f`, `g` and `n`. The
split source's actual cocharacter lattice is torsion-free, so multiplication by
`n` implies injectivity of the actual integral map. The split target's actual
cocharacter lattice is finitely generated, and its cokernel is annihilated by
`n`, hence finite. After tensoring with the rationals or reals, `n` is
invertible, so the reverse map divided by `n` gives bijectivity. The final
proposition uses the published actual maps throughout; coordinate choices are
used only to construct the intermediate actual reverse homomorphism.

This proof combines the character comparison and geometric realization by
Worker 384 with the integral quasiinverse algebra and actual cocharacter
conclusion helper by Worker 1444. The paired proof describes the implemented
route using the named Library results; it asserts no additional descent or
non-split comparison.
