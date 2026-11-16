# Simultaneous local splitting of two supplied maximal tori

This internal refinement of `SuppliedTorusLocalSplitting` proves that one
may split two supplied maximal tori simultaneously near any point of the
base, keeping each original inclusion. It combines the single-torus
construction with the published base-change theorems for full fibrewise
coordinate root data and actual exponent weight spaces.

`HasSplitMaximalTorusCoordinates.baseChange` preserves aligned split data
under every homomorphism of commutative rings, with a smooth affine
ambient group. The coordinate root datum is unchanged. Each root line
after base change is the scalar extension of the original actual weight
space, by `exponentWeightBaseChangeEquiv`; extending its given
trivialization therefore gives a free line on the new base.
`baseChange_affine` uses the coefficient homomorphism of any supplied
morphism between affine schemes. `flatten_baseChange` transports
successive pullbacks to the direct pullback using naturality of the
base-change composition isomorphisms.

`HaveCommonEtaleLocalSplitCoordinates i j` says that at every base point
there is one affine étale neighbourhood with
`HasSplitMaximalTorusCoordinates` for both pulled-back inclusions.
`commonEtaleLocalSplitCoordinates_of_suppliedTori` proves this for any two
reductive groups over any scheme and supplied closed relative tori
maximal on every residue fibre. The proof first splits the first torus.
It then applies the single-torus theorem to the second torus over the
first neighbourhood. The first set of coordinates survives this further
base change, and composition comparisons identify both resulting
inclusions with direct pullbacks of the original maps.

The two coordinate root data need not be identified with each other.
Compatibility of isogenies with those root data and local existence of
torus conjugators are separate proof obligations. There is no
reducedness, connectedness or noetherian hypothesis on the base.
