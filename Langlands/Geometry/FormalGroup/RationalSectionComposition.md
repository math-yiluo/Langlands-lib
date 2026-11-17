# Composition on rational formal Hom sheaf sections

This internal construction extends the existing tensor composition to sections
of the actual Zariski rational Hom sheaves. The coefficient ring O is any
commutative ring, R is an O-algebra, and F is an O-algebra field. R and F share
a universe; O may have a different universe. The finite coordinate types of
the formal modules may differ.

The underlying type presheaf, underlying type sheaf, and genuine module
sheafification unit are exposed as `rationalHomTypePresheaf`,
`rationalHomTypeSheaf`, and `rationalHomTypeUnit`. The natural map
`rationalHomCompositionPresheaf` applies the previously constructed tensor
composition to each pair of sections. Its naturality follows from the proved
compatibility of tensor composition with actual coefficient restriction,
including the identity-coordinate comparisons of the formal modules.

Each sheafification unit is locally injective and locally surjective, and
these properties persist after forgetting the module structure. The generic
`SheafifyPairing.extend` construction therefore extends the presheaf pairing
uniquely into the underlying rational Hom sheaf. Evaluating this extension
on an open set defines `RationalSection.comp`. The operation is constructed
from the actual sheafification, rather than supplied as data.

`comp_ofRational` is the agreement law for the extension. It identifies
composition of images of tensor sections with the image of their tensor
composition. `restrict_comp_hom` is the naturality law of the extension.
This construction makes no assertion that every sheaf section is the image
of a tensor section over the whole open set.

The provenance is internal, using the existing formal Hom algebra and genuine
sheafification. No representability, finite-kernel, nilpotent rigidity, or
identification with a separately defined formal-scheme Hom sheaf is asserted.
