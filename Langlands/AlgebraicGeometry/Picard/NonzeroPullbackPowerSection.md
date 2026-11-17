# Power sections of nonzero endomorphism pullbacks

This internal geometric construction is over an arbitrary field in universe `u`. For an actual abelian scheme `A` over the field, `NonzeroPullbackPowerSection A L f` says that a positive tensor power of the pullback of `L` along the underlying scheme map of `f` has a global section with a frame point and a nonframe point.

The proof first shows that a homomorphism whose underlying point image lies in the image of the unit section is zero. The abelian variety is integral and hence reduced. The published reduced-source factorization through a section over a one-point scheme factors the map through the unit, and extensionality identifies it with the actual zero homomorphism.

For nonzero `f` there is therefore a point whose image lies outside the unit section. This section has closed image. The ample-section basis theorem produces a section of a positive power of `L` that frames at that image point and whose entire frame open avoids the unit section. Actual section pullback, transported through the pullback tensor-power isomorphism, frames at the chosen source point. Preservation of the unit section by `f` proves that the pullback section does not frame at the identity point.

The construction uses existing geometric and section theorems and has no external-source claim. It asserts no trace formula or Rosati positivity theorem.
