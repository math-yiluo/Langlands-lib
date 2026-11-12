# Relative Cartier kernel duality as group-valued functors

Author: Worker 195.

This internal construction packages the published proposition
`RelativeDualKernelCharacterBijectiveStatement` as an explicit theorem
dependency `duality`. It retains all seven tensor/Picard propositions,
both actual dual-scheme witnesses, inverse Poincare line bundles and
evaluation isomorphisms of the existing character constructor.
There is no field, reducedness, noetherian, separability or
invertible-degree restriction on the base `S`, test scheme `T`, or
actual isogeny `f : A ⟶ B`.

`relativeDualKernelCharacterEquiv` applies `AddEquiv.ofBijective` to
the existing normalized additive character and the exact component
of `duality`. `relativeDualKernelCartierIso` packages these equivalences
as an isomorphism from the actual additive point functor of the kernel
of the constructed dual homomorphism to `Cartier.characters` of the
actual kernel of `f`. Naturality is the published restriction law
for the same geometric character. The `_apply` and `_hom` identities
show that the forward map is precisely that character.

`relativeDualKernelCharacterHomIso` composes with the published
`Cartier.characterHomNatIso`, obtaining actual homomorphisms
from the base-changed primal kernel to the multiplicative group
over each test scheme. `relativeDualKernelCharacter_existsUnique`
recovers a unique actual dual-kernel point for every character,
including nonreduced test schemes.

This is the arbitrary-base analogue of the published field packaging
in `KernelCartierDuality`. The relative bijectivity proposition remains
an explicit input, rather than an arbitrary selected isomorphism.
Its independent proof is a separate obligation; this module alone
does not establish that proposition. No existence or geometry of the
dual, isogeny assertion for the dual map, numerical rank, or
polarization perfectness is concluded here. The original normalized
character and the derived relative target are documented in the
unchanged `RelativeDualKernelCharacterBijectiveStatement` pair.
